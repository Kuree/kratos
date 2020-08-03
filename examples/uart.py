# uart implementation is translated
# from https://www.nandland.com/vhdl/modules/module-uart-serial-port-rs232.html

from kratos import Generator, always_ff, verilog, posedge


class UartBase(Generator):
    def __init__(self, name, debug=False):
        super().__init__(name, debug)
        # create some common variables
        # ports
        self.clk = self.clock("clk")
        # parameters
        self.clks_per_bit = self.parameter("CLKS_PER_BIT", 8,
                                           initial_value=87)
        # FSM
        self.fsm_states = self.get_state_enum()
        # create an enum variable based on the enum definition
        self._sm_main = self.enum_var("sm_main", self.fsm_states)
        self._clock_count = self.var("clock_count", 8)
        self._bit_index = self.var("bit_index", 3)

    def get_state_enum(self):
        # rx and tx share the same FSM
        return self.enum("STATE",
                         {
                             "IDLE": 0,
                             "START_BIT": 1,
                             "DATA_BITS": 2,
                             "STOP_BIT": 3,
                             "CLEANUP": 4
                         })


class UartRx(UartBase):
    def __init__(self):
        super().__init__("UartRx")

        # ports
        self.rx_serial = self.input("rx_serial", 1)
        self.rx_dv = self.output("rx_dv", 1)
        self.rx_byte = self.output("rx_byte", 8)

        # variables
        self._rx_data_r = self.var("rx_data_r", 1)
        self._rx_data = self.var("rx_data", 1)

        self._rx_byte = self.var("_rx_byte", 8)
        self._rx_dv = self.var("_rx_dv", 1)

        # always blocks
        self.add_always(self.rx_data)
        self.add_always(self.fsm_control, state=self.fsm_states)

        # assign output
        self.add_stmt(self.rx_dv.assign(self._rx_dv))
        self.add_stmt(self.rx_byte.assign(self._rx_byte))

    # double register
    @always_ff((posedge, "clk"))
    def rx_data(self):
        self._rx_data_r = self.rx_serial
        self._rx_data = self._rx_data_r

    @always_ff((posedge, "clk"))
    def fsm_control(self, state):
        # FSM control. use state variable allows different state enum encoding
        # if ... elif ... else ... will be converted into unique case
        # automatically during code generation
        if self._sm_main == state.IDLE:
            self._rx_dv = 0
            self._clock_count = 0
            self._bit_index = 0
            if self.rx_data == 0:
                self._sm_main = state.START_BIT
            else:
                self._sm_main = state.IDLE
        elif self._sm_main == state.START_BIT:
            if self._clock_count == (self.clks_per_bit - 1) / 2:
                if self._rx_data == 0:
                    self._clock_count = 0
                    self._sm_main = state.DATA_BITS
                else:
                    self._sm_main = state.IDLE
            else:
                self._clock_count += 1
                self._sm_main = state.START_BIT
        elif self._sm_main == state.DATA_BITS:
            if self._clock_count < self.clks_per_bit - 1:
                self._clock_count += 1
                self._sm_main = state.DATA_BITS
            else:
                self._clock_count = 0
                self._rx_byte[self._bit_index] = self._rx_data

                if self._bit_index < 7:
                    self._bit_index += 1
                    self._sm_main = state.DATA_BITS
                else:
                    self._bit_index = 0
                    self._sm_main = state.STOP_BIT
        elif self._sm_main == state.STOP_BIT:
            if self._clock_count < (self.clks_per_bit - 1):
                self._clock_count += 1
                self._sm_main = state.STOP_BIT
            else:
                self._rx_dv = 1
                self._clock_count = 0
                self._sm_main = state.CLEANUP
        elif self._sm_main == state.CLEANUP:
            self._sm_main = state.IDLE
            self._rx_dv = 0
        else:
            self._sm_main = state.IDLE


class UartTx(UartBase):
    def __init__(self):
        super().__init__("UartTx")

        # ports
        self.tx_dv = self.input("tx_dv", 1)
        self.tx_byte = self.input("tx_byte", 8)
        self.tx_active = self.output("tx_active", 1)
        self.tx_serial = self.output("tx_serial", 1)
        self.tx_done = self.output("tx_done", 1)

        # variables
        self._tx_data = self.var("_tx_data", 8)
        self._tx_done = self.var("_tx_done", 1)
        self._tx_active = self.var("_tx_active", 1)

        # add always block
        self.add_always(self.sm_main, state=self.fsm_states)

        # assign output
        self.add_stmt(self.tx_active.assign(self._tx_active))
        self.add_stmt(self.tx_done.assign(self._tx_done))

    @always_ff((posedge, "clk"))
    def sm_main(self, state):
        if self._sm_main == state.IDLE:
            self.tx_serial = 1
            self._tx_done = 0
            self._clock_count = 0
            self._bit_index = 0

            if self.tx_dv == 1:
                self._tx_active = 1
                self._tx_data = self.tx_byte
                self._sm_main = state.START_BIT
            else:
                self._sm_main = state.IDLE
        elif self._sm_main == state.START_BIT:
            self.tx_serial = 0

            if self._clock_count < (self.clks_per_bit -1):
                self._clock_count += 1
                self._sm_main = state.START_BIT
            else:
                self._clock_count = 0
                self._sm_main = state.DATA_BITS
        elif self._sm_main == state.DATA_BITS:
            self.tx_serial = self._tx_data[self._bit_index]

            if self._clock_count < self.clks_per_bit - 1:
                self._clock_count += 1
                self._sm_main = state.DATA_BITS
            else:
                self._clock_count = 0

                if self._bit_index < 7:
                    self._bit_index += 1
                    self._sm_main = state.DATA_BITS
                else:
                    self._bit_index = 0
                    self._sm_main = state.STOP_BIT
        elif self._sm_main == state.STOP_BIT:
            self.tx_serial = 1

            if self._clock_count < self.clks_per_bit - 1:
                self._clock_count += 1
                self._sm_main = state.STOP_BIT
            else:
                self._tx_done = 1
                self._clock_count = 0
                self._sm_main = state.CLEANUP
                self._tx_active = 0
        elif self._sm_main == state.CLEANUP:
            self._tx_done = 1
            self._sm_main = state.IDLE
        else:
            self._sm_main = state.IDLE


if __name__ == "__main__":
    verilog(UartRx(), filename="UartRx.sv")
    verilog(UartTx(), filename="UartTx.sv")
