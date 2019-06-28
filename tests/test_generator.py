from kratos import Generator, PortDirection, PortType, BlockEdgeType, always, \
    verilog


def test_generator():
    mods = []
    for i in range(10):
        mod = Generator("mod1", f"a{i}")
        mods.append(mod)

    for idx, mod in enumerate(mods):
        assert mod.name == "mod1"
        mod.name = f"new_mod{idx}"
        assert mod.name == f"new_mod{idx}"


def test_async_reg():
    class AsyncReg(Generator):
        def __init__(self, width):
            super().__init__("register", "reg1")

            # define inputs and outputs
            self._in = self.port("in", width, PortDirection.In)
            self._out = self.port("out", width, PortDirection.Out)
            self._clk = self.port("clk", 1, PortDirection.In, PortType.Clock)
            self._rst = self.port("rst", 1, PortDirection.In,
                                  PortType.AsyncReset)
            self._val = self.var("val", width)

            # add combination and sequential blocks
            self.add_seq(self.seq_code_block)

            self.add_comb(self.comb_code_block)

        @always([(BlockEdgeType.Posedge, "clk"),
                 (BlockEdgeType.Posedge, "rst")])
        def seq_code_block(self):
            if ~self._rst:
                self._val = 0
            else:
                self._val = self._in

        def comb_code_block(self):
            self._out = self._val

    reg_width = 16
    reg = AsyncReg(reg_width)
    # produce verilog
    verilog_src = verilog(reg)
    assert "register" in verilog_src
    reg_src = verilog_src["register"]
    assert reg_src != ""
    # TODO:
    #  add a util function to check generated verilog


if __name__ == "__main__":
    test_async_reg()
