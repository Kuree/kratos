from kratos import Generator, PortDirection, PortType, BlockEdgeType, always, \
    verilog, is_valid_verilog
from kratos.passes import uniquify_generators, hash_generators


def test_generator():
    mods = []
    for i in range(10):
        mod = Generator("mod1")
        mod.instance_name = f"a{i}"
        mods.append(mod)

    for idx, mod in enumerate(mods):
        assert mod.name == "mod1"
        mod.name = f"new_mod{idx}"
        assert mod.name == f"new_mod{idx}"


class AsyncReg(Generator):
    def __init__(self, width):
        super().__init__("register")

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


def test_async_reg():
    reg_width = 16
    reg = AsyncReg(reg_width)
    # produce verilog
    verilog_src = verilog(reg)
    assert "register" in verilog_src
    reg_src = verilog_src["register"]
    assert is_valid_verilog(reg_src)


def test_module_unique():
    reg1 = AsyncReg(16)
    reg2 = AsyncReg(1)
    reg2.instance_name = "test"
    parent = Generator("top")
    parent.add_child_generator(reg1)
    parent.add_child_generator(reg2)

    hash_generators(parent)
    c = Generator.get_context()
    reg1_hash = c.get_hash(reg1.internal_generator)
    reg2_hash = c.get_hash(reg2.internal_generator)
    assert reg1_hash != reg2_hash

    uniquify_generators(parent)
    assert reg1.internal_generator.name != reg2.internal_generator.name
    assert reg1.name != reg2.name


if __name__ == "__main__":
    test_async_reg()
