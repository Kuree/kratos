from kratos import Generator, PortDirection, PortType, BlockEdgeType, always, \
    verilog, is_valid_verilog, VarException, StmtException, ASTVisitor, \
    PackedStruct, Port
from kratos.passes import uniquify_generators, hash_generators
import os
import tempfile


class PassThroughMod(Generator):
    def __init__(self, is_clone: bool = False):
        super().__init__("mod1", True, is_clone)
        self.in_ = self.port("in", 1, PortDirection.In)
        self.out_ = self.port("out", 1, PortDirection.Out)
        self.wire(self.out_, self.in_)


class PassThroughTop(Generator):
    def __init__(self):
        super().__init__("top", True)

        self.port("in", 1, PortDirection.In)
        self.port("out", 1, PortDirection.Out)

        pass_through = PassThroughMod()
        self.add_child_generator("pass", pass_through)
        self.wire(self["pass"].ports["in"], self.ports["in"], )

        self.wire(self.ports.out, self["pass"].ports.out)


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
    mod = PassThroughTop()
    # turn off pass through module optimization since it will remove
    # mod2 completely
    mod_src = verilog(mod, optimize_passthrough=False)
    assert "mod1" in mod_src
    assert "top" in mod_src
    mod2_src = mod_src["top"]
    assert "$" not in mod2_src
    assert is_valid_verilog(mod_src["top"])
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
    mod = PassThroughTop()
    # turn off pass through module optimization since it will remove
    # mod2 completely
    mod_src = verilog(mod, optimize_passthrough=True)
    assert "top" in mod_src
    assert "mod1" not in mod_src
    assert is_valid_verilog(mod_src["top"])
    assert "mod1" not in mod_src["top"]


def test_nested_if():
    class Mod(Generator):
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

    mod = Mod()
    mod_src = verilog(mod)
    src = mod_src["mod1"]
    assert is_valid_verilog(src)


def test_fanout_mod_inst():
    class Mod2(Generator):
        def __init__(self):
            super().__init__("mod2")
            self.in_ = self.port("in", 1, PortDirection.In)
            self.out_ = self.port("out", 1, PortDirection.Out)

            self.mod_1 = PassThroughMod()
            self.mod_2 = PassThroughMod()

            self.add_child_generator("mod1", self.mod_1)
            self.add_child_generator("mod2", self.mod_2)

            self.wire(self.in_, self.mod_1.in_)
            self.wire(self.in_, self.mod_2.in_)

            self.add_code(self.code)

        def code(self):
            self.out_ = self.mod_1.out_ + self.mod_2.out_

    mod = Mod2()
    mod_src = verilog(mod, optimize_passthrough=False)
    assert "mod2" in mod_src
    src = mod_src["mod2"]
    assert is_valid_verilog(src)


def test_debug():
    class Mod(Generator):
        def __init__(self):
            super().__init__("mod1", True)
            self.in_ = self.port("in", 1, PortDirection.In)
            self.out_1 = self.port("out1", 1, PortDirection.Out)
            self.out_2 = self.port("out2", 1, PortDirection.Out)

            self.wire(self.out_1, self.in_)

            self.add_code(self.code)

        def code(self):
            self.out_2 = self.in_

    mod = Mod()
    mod_src, mod_debug = verilog(mod, debug=True)
    src_mapping = mod_debug["mod1"]
    assert len(src_mapping) == 7
    verilog_lines = mod_src["mod1"].split("\n")
    verilog_ln = 0
    for ln, line in enumerate(verilog_lines):
        if "assign out1 = in;" in line:
            verilog_ln = ln + 1
            break
    fn, ln = src_mapping[verilog_ln][0]
    with open(fn) as f:
        python_lns = f.readlines()
    assert "self.wire(self.out_1, self.in_)" in python_lns[ln - 1]


def test_illegal_assignment_width():
    class Mod(Generator):
        def __init__(self):
            super().__init__("mod1", True)
            self.in_ = self.port("in", 1, PortDirection.In)
            self.out_ = self.port("out", 4, PortDirection.Out)

            self.add_code(self.code)

        def code(self):
            if self.in_ == self.const(1, 1):
                self.out_ = self.const(1, 4)
            else:
                self.out_ = self.const(1, 1)

    try:
        Mod()
        assert False
    except VarException as ex:
        print(ex)
        assert True


def test_illegal_assignment_blocking():
    class Mod(Generator):
        def __init__(self):
            super().__init__("mod1", True)
            self.in_ = self.port("in", 1, PortDirection.In)
            self.out_ = self.port("out", 1, PortDirection.Out)
            self.clk_ = self.port("clk", 1, PortDirection.In, PortType.Clock)

            self.wire(self.out_, self.in_)

            self.add_code(self.code)

        @always([(BlockEdgeType.Posedge, "clk")])
        def code(self):
            self.out_ = 1

    try:
        mod = Mod()
        verilog(mod)
        assert False
    except StmtException as ex:
        print(ex)
        assert True


def test_data_if():
    class Mod(Generator):
        def __init__(self, bool_flag):
            super().__init__("mod1")
            self.in_ = self.port("in", 1, PortDirection.In)
            self.out_ = self.port("out", 1, PortDirection.Out)
            self.bool_flag = bool_flag

            self.add_code(self.code)

        def code(self):
            if self.bool_flag:
                if self.in_ == self.const(1, 1):
                    self.out_ = 1
                else:
                    self.out_ = 0
            else:
                if self.in_ == self.const(0, 1):
                    self.out_ = 0
                else:
                    self.out_ = 1

    mod = Mod(True)
    mod_src = verilog(mod)
    src = mod_src["mod1"]
    assert is_valid_verilog(src)
    assert "in == 1'h1" in src
    # need to clear the context, otherwise it will be a different module name
    Generator.clear_context()
    mod = Mod(False)
    mod_src = verilog(mod)
    src = mod_src["mod1"]
    assert is_valid_verilog(src)
    assert "in == 1'h0" in src


def test_static_eval_for_loop():
    class Mod(Generator):
        def __init__(self, num_loop):
            super().__init__("mod1", True)
            self.in_ = self.port("in", 1, PortDirection.In)
            self.out_ = self.port("out", num_loop, PortDirection.Out)
            self.num_loop = num_loop

            self.add_code(self.code)

        def code(self):
            if self.in_ == self.const(1, 1):
                for i in range(self.num_loop):
                    self.out_[i] = 1
            else:
                for i in range(self.num_loop):
                    self.out_[i] = 0

    loop = 4
    mod = Mod(loop)
    mod_src, mod_debug = verilog(mod, debug=True)
    src = mod_src["mod1"]
    mod_mapping = mod_debug["mod1"]
    lines = list(mod_mapping.keys())
    lines.sort()
    for ii in range(len(mod_mapping) - loop, len(mod_mapping) - 1):
        assert mod_mapping[lines[-1]][-1] == mod_mapping[lines[ii]][-1]
    assert is_valid_verilog(src)


def test_pass():
    def change_name(generator):
        class Visitor(ASTVisitor):
            def __init__(self):
                ASTVisitor.__init__(self)

            def visit(self, node):
                if isinstance(node, Port):
                    # rename the output port
                    if node.name == "out":
                        node.name = "test"

        visitor = Visitor()
        visitor.visit_root(generator)

    class Mod1(Generator):
        def __init__(self):
            super().__init__("mod1", True)
            self.in_ = self.port("in", 1, PortDirection.In)
            self.out_ = self.port("out", 1, PortDirection.Out)
            self.wire(self.out_, self.in_)

    mod = Mod1()
    mod_src = verilog(mod, additional_passes={"name_change": change_name})
    src = mod_src["mod1"]
    assert is_valid_verilog(src)
    assert "logic  test" in src


def test_const_port():
    class Mod(Generator):
        def __init__(self):
            super().__init__("mod")

            self.in_ = self.port("in", 1, PortDirection.In)
            self.out_ = self.port("out", 2, PortDirection.Out)

            self.child = PassThroughMod()
            self.add_child_generator("child", self.child)
            self.child.wire(self.child.in_, self.const(0, 1))
            self.wire(self.out_[0], self.child.out_)
            self.wire(self.out_[1], self.in_)

    mod = Mod()
    mod_src = verilog(mod, optimize_passthrough=False)
    assert "mod" in mod_src
    src = mod_src["mod"]
    assert is_valid_verilog(src)


def test_create():
    class Mod(Generator):
        def __init__(self, width, is_clone=False):
            super().__init__(f"mod_{width}", is_clone=is_clone)

            self.in_ = self.port("in", width, PortDirection.In)
            self.out_ = self.port("out", width, PortDirection.Out)
            self.wire(self.out_, self.in_)

    mod1 = Mod.create(width=1)
    mod2 = Mod.create(width=2)
    mod3 = Mod.create(width=1)

    assert not mod1.is_cloned
    assert not mod2.is_cloned
    assert mod3.is_cloned

    # modify mod 3
    mod3.initialize_clone()
    mod3.in_.width = 3
    mod3.out_.width = 3
    assert not mod3.is_cloned
    mod_src = verilog(mod3)

    # we didn't change the name
    assert "mod_1" in mod_src
    assert "2:0" in mod_src["mod_1"]
    assert is_valid_verilog(mod_src["mod_1"])


def test_packed_struct():
    struct = PackedStruct("config_data", [("read", 16, False),
                                          ("data", 16, False)])

    class Mod(Generator):
        def __init__(self):
            super().__init__("mod")
            self.port_packed("in", PortDirection.In, struct)
            self.port_packed("out", PortDirection.Out, struct)
            self.wire(self.ports["out"], self.ports["in"])

    mod = Mod()
    mod_src, struct_def = verilog(mod, optimize_passthrough=False,
                                  extra_struct=True)
    src = mod_src["mod"]
    struct_src = struct_def["config_data"]
    src = struct_src + "\n" + src
    assert is_valid_verilog(src)


def test_more_debug1():
    mod = PassThroughTop()
    mod_src, debug_info = verilog(mod, debug=True)
    src = mod_src["top"]
    debug = debug_info["top"]
    assert is_valid_verilog(src)
    assert len(debug) > 3


def test_more_debug2():
    class Top(Generator):
        def __init__(self):
            super().__init__("top", True)

            self.port("in", 1, PortDirection.In)
            self.port("out", 1, PortDirection.Out)

            pass_through = PassThroughMod()
            self.add_child_generator("pass", pass_through)
            self.wire(self["pass"].ports["in"], self.ports["in"], )

            self.add_code(self.code_block)

        def code_block(self):
            self.ports.out = self["pass"].ports.out

    mod = Top()
    mod_src, debug_info = verilog(mod, debug=True)
    src = mod_src["top"]
    debug = debug_info["top"]
    assert is_valid_verilog(src)
    assert len(debug) > 3


def test_verilog_file():
    mod = PassThroughTop()
    with tempfile.TemporaryDirectory() as tempdir:
        filename = os.path.join(tempdir, "mod.sv")
        verilog(mod, filename=filename, debug=True, optimize_passthrough=False)
        with open(filename) as f:
            src = f.read()
            assert is_valid_verilog(src)


if __name__ == "__main__":
    test_create()
