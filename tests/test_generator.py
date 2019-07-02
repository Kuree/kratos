from kratos import Generator, PortDirection, PortType, BlockEdgeType, always, \
    verilog, is_valid_verilog
from kratos.passes import uniquify_generators, hash_generators
import os


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
        self.add_code(self.seq_code_block)

        self.add_code(self.comb_code_block)

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
    parent.add_child_generator("reg1", reg1)
    parent.add_child_generator("reg2", reg2)

    hash_generators(parent)
    c = Generator.get_context()
    reg1_hash = c.get_hash(reg1.internal_generator)
    reg2_hash = c.get_hash(reg2.internal_generator)
    assert reg1_hash != reg2_hash

    uniquify_generators(parent)
    assert reg1.internal_generator.name != reg2.internal_generator.name
    assert reg1.name != reg2.name


def test_else_if():
    class ElseIf(Generator):
        def __init__(self):
            super().__init__("elseif")
            self._in0 = self.port("in0", 1, PortDirection.In)
            self._in1 = self.port("in1", 1, PortDirection.In)
            self._out = self.port("out", 1, PortDirection.Out)

            self.add_code(self.else_if)

        def else_if(self):
            if self._in0 == self.const(1, 1):
                self._out = 1
            elif self._in1 == self.const(1, 1):
                self._out = 0
            else:
                self._out = 1

    mod = ElseIf()
    mod_src = verilog(mod)
    assert "elseif" in mod_src
    src = mod_src["elseif"]
    assert is_valid_verilog(src)


def test_mod_instantiation():
    class Mod1(Generator):
        def __init__(self):
            super().__init__("mod1")
            self.in_ = self.port("in", 1, PortDirection.In)
            self.out_ = self.port("out", 1, PortDirection.Out)
            self.wire(self.out_, self.in_)

    class Mod2(Generator):
        def __init__(self):
            super().__init__("mod2")
            self._in = self.port("in", 1, PortDirection.In)
            self._out = self.port("out", 1, PortDirection.Out)

            self.add_child_generator("mod1", Mod1())

            self.wire(self["mod1"].in_, self._in)
            self.wire(self._out, self["mod1"].out_)

    mod = Mod2()
    # turn off pass through module optimization since it will remove
    # mod2 completely
    mod_src = verilog(mod, optimize_passthrough=False)
    assert "mod1" in mod_src
    assert "mod2" in mod_src
    assert is_valid_verilog(mod_src["mod2"])
    assert is_valid_verilog(mod_src["mod1"])


def test_external_module():
    src_file = os.path.join(os.path.dirname(__file__), "vectors", "module1.sv")
    mod = Generator.from_verilog("module1", src_file, [], {})
    assert mod.internal_generator.external_filename() == src_file
    assert mod.name == "module1"
    assert mod.internal_generator.external()
    hash_generators(mod)
    c = Generator.get_context()
    assert c.has_hash(mod.internal_generator)
    assert c.get_hash(mod.internal_generator) != 0


def test_for_loop():
    class Module(Generator):
        def __init__(self, num_var: int):
            super().__init__("mod")
            self.num_var = num_var

            self.inputs = []
            for i in range(num_var):
                self.inputs.append(self.port(f"in{i}", 1, PortDirection.In))
            self.output = self.port("out", num_var, PortDirection.Out)

            self.add_code(self.code_block)

        def code_block(self):
            for i in range(self.num_var):
                self.output[i] = self.inputs[i]

    mod = Module(4)
    mod_src = verilog(mod)
    src = mod_src["mod"]
    assert is_valid_verilog(src)


def test_switch():
    class Switch(Generator):
        def __init__(self):
            super().__init__("switch_test")

            self._in = self.port("in", 3, PortDirection.In)
            self._out = self.port("out", 3, PortDirection.Out)

            self.add_code(self.logic)

        def logic(self):
            if self._in == self.const(0, 3):
                self._out = 0
            elif self._in == self.const(1, 3):
                self._out = 1
            else:
                self._out = 2

    mod = Switch()
    mod_src = verilog(mod)
    src = mod_src["switch_test"]
    assert is_valid_verilog(src)


def test_pass_through():
    class Mod1(Generator):
        def __init__(self):
            super().__init__("mod1")
            self.in_ = self.port("in", 1, PortDirection.In)
            self.out_ = self.port("out", 1, PortDirection.Out)
            self.wire(self.out_, self.in_)

    class Mod2(Generator):
        def __init__(self):
            super().__init__("mod2")
            self._in = self.port("in", 1, PortDirection.In)
            self._out = self.port("out", 1, PortDirection.Out)

            mod1 = Mod1()
            self.add_child_generator("mod1", mod1)
            self.wire(mod1.in_, self._in)
            self.wire(self._out, mod1.out_)

    mod = Mod2()
    # turn off pass through module optimization since it will remove
    # mod2 completely
    mod_src = verilog(mod, optimize_passthrough=True)
    assert "mod2" in mod_src
    assert "mod1" not in mod_src
    assert is_valid_verilog(mod_src["mod2"])
    assert "mod1" not in mod_src["mod2"]


def test_nested_if():
    class Mod1(Generator):
        def __init__(self):
            super().__init__("mod1")
            self.in_ = self.port("in", 2, PortDirection.In)
            self.out_ = self.port("out", 2, PortDirection.Out)

            self.add_code(self.nested_if)

        def nested_if(self):
            if self.in_ < self.const(1, 2):
                if self.in_ < self.const(2, 2):
                    self.out_ = 1
                else:
                    self.out_ = 3
            else:
                self.out_ = 2

    mod = Mod1()
    mod_src = verilog(mod)
    src = mod_src["mod1"]
    assert is_valid_verilog(src)


def test_fanout_mod_inst():
    class Mod1(Generator):
        def __init__(self):
            super().__init__("mod1")
            self.in_ = self.port("in", 1, PortDirection.In)
            self.out_ = self.port("out", 1, PortDirection.Out)
            self.wire(self.out_, self.in_)

    class Mod2(Generator):
        def __init__(self):
            super().__init__("mod2")
            self.in_ = self.port("in", 1, PortDirection.In)
            self.out_ = self.port("out", 1, PortDirection.Out)

            self.mod_1 = Mod1()
            self.mod_2 = Mod1()

            self.add_child_generator("mod1", self.mod_1)
            self.add_child_generator("mod2", self.mod_2)

            self.wire()



if __name__ == "__main__":
    test_pass_through()
