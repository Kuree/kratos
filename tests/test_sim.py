from kratos import Simulator, Generator, posedge, always


def test_sim_reg():
    class AsyncReg(Generator):
        def __init__(self, width, debug=False):
            super().__init__("Register", debug)

            self.in_ = self.input("in", width)
            self.out = self.output("out", width)
            self.clk = self.clock("clk")
            self.rst = self.reset("rst")

            self.add_code(self.seq_code_block)

        @always((posedge, "clk"), (posedge, "rst"))
        def seq_code_block(self):
            if self.rst:
                self.out = 0
            else:
                self.out = self.in_

    reg = AsyncReg(16)
    sim = Simulator(reg)
    val = sim.get(reg.out)
    assert val is None
    # reset
    sim.reset()
    val = sim.get(reg.out)
    assert val == 0
    # put in some values
    for v in range(1, 4 + 1):
        sim.set(reg.in_, v)
        val = sim.get(reg.out)
        # 1 cycle delay
        assert val == v - 1
        # toggle the clock
        sim.cycle()
        val = sim.get(reg.out)
        assert val == v


if __name__ == "__main__":
    test_sim_reg()
