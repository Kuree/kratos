from kratos import Generator, PortDirection, PortType, always_ff, \
    verilog, is_valid_verilog, VarException, StmtException, \
    PackedStruct, Attribute, ext, posedge, PortBundle, const, comment, \
    enable_runtime_debug, always_comb
from _kratos.passes import uniquify_generators, hash_generators_parallel
import os
import tempfile
import shutil
import pytest
import platform
import kratos

no_verilator = shutil.which("verilator") is None
is_windows = platform.system() == "Windows"


class PassThroughMod(Generator):
    def __init__(self, is_clone: bool = False):
        super().__init__("mod1", True, is_clone)
        self.in_ = self.input("in", 1)
        self.out_ = self.output("out", 1)
        self.wire(self.out_, self.in_)


class PassThroughTop(Generator):
    def __init__(self):
        super().__init__("top", True)

        self.input("in", 1)
        self.output("out", 1)

        pass_through = PassThroughMod()
        self.add_child("pass", pass_through)
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
    def __init__(self, width, debug=False):
        super().__init__("register", debug)

        # define inputs and outputs
        self._in = self.input("in", width)
        self._out = self.output("out", width)
        self._clk = self.clock("clk")
        self._rst = self.reset("rst")
        self._val = self.var("val", width)

        # add combination and sequential blocks
        self.add_always(self.seq_code_block)

        self.add_always(self.comb_code_block)

    @always_ff((posedge, "clk"), (posedge, "rst"))
    def seq_code_block(self):
        if self._rst:
            self._val = 0
        else:
            self._val = self._in

    @always_comb
    def comb_code_block(self):
        self._out = self._val


def test_async_reg(check_gold):
    reg_width = 16
    reg = AsyncReg(reg_width)
    check_gold(reg, "test_async_reg")
    assert "in" in reg.ports
    assert "val" in reg.vars


def test_module_unique():
    reg1 = AsyncReg(16)
    reg2 = AsyncReg(1)
    reg2.instance_name = "test"
    parent = Generator("top")
    parent.add_child("reg1", reg1)
    parent.add_child("reg2", reg2)

    hash_generators_parallel(parent.internal_generator)
    c = Generator.get_context()
    reg1_hash = c.get_hash(reg1.internal_generator)
    reg2_hash = c.get_hash(reg2.internal_generator)
    assert reg1_hash != reg2_hash

    uniquify_generators(parent.internal_generator)
    assert reg1.internal_generator.name != reg2.internal_generator.name
    assert reg1.name != reg2.name


@pytest.mark.skipif(no_verilator, reason="verilator not available")
def test_wire_const():
    mod = Generator("test")
    out_ = mod.output("out", 1)
    mod.wire(out_, 1)

    mod_src = verilog(mod)
    assert is_valid_verilog(mod_src)


def test_else_if(check_gold):
    class ElseIf(Generator):
        def __init__(self):
            super().__init__("elseif")
            self._in0 = self.port("in0", 1, PortDirection.In)
            self._in1 = self.port("in1", 1, PortDirection.In)
            self._out = self.port("out", 1, PortDirection.Out)

            self.add_always(self.else_if)

        @always_comb
        def else_if(self):
            if self._in0 == const(1, 1):
                self._out = 1
            elif self._in1 == const(1, 1):
                self._out = 0
            else:
                self._out = 1

    mod = ElseIf()
    check_gold(mod, "test_else_if")


def test_mod_instantiation(check_gold):
    mod = PassThroughTop()
    # turn off pass through module optimization since it will remove
    # mod2 completely
    check_gold(mod, "test_mod_instantiation", optimize_passthrough=False)


def test_external_module():
    src_file = os.path.join(os.path.dirname(__file__), "vectors", "module1.sv")
    mod = Generator.from_verilog("module1", src_file, [], {})
    assert mod.internal_generator.external_filename() == src_file
    assert mod.name == "module1"
    assert mod.internal_generator.external()
    hash_generators_parallel(mod.internal_generator)
    c = Generator.get_context()
    assert c.has_hash(mod.internal_generator)
    assert c.get_hash(mod.internal_generator) != 0


class ForLoopModule(Generator):
    def __init__(self, num_var: int, debug: bool, loop_input: bool):
        super().__init__("mod", debug)
        self.num_var = num_var
        self.loop_input = loop_input
        if self.loop_input:
            self.inputs = []
            for i in range(num_var):
                self.inputs.append(self.port(f"in{i}", 1, PortDirection.In))
            self.out = self.output("out", num_var)
        else:
            self.out = self.output("out", num_var, size=num_var)

        self.add_always(self.code_block)

    @always_comb
    def code_block(self):
        for i in range(self.num_var):
            if self.loop_input:
                self.out[i] = self.inputs[i]
            else:
                self.out[i] = i


def test_for_loop_debug(check_gold):
    mod = ForLoopModule(4, True, True)
    check_gold(mod, "test_for_loop")


def test_for_loop_no_debug_unroll(check_gold):
    # because self.inputs is not a kratos variable, it should unroll
    mod = ForLoopModule(4, False, True)
    check_gold(mod, "test_for_loop")


def test_for_loop_no_unroll(check_gold):
    mod = ForLoopModule(4, False, False)
    check_gold(mod, "test_for_loop_no_unroll")


def test_for_bit_index():
    class Mod(Generator):
        def __init__(self, num_loop):
            super().__init__("mod")
            self.out_ = self.output("out", num_loop)
            self.num_loop = num_loop

            self.add_always(self.code)

        @always_comb
        def code(self):
            for i in range(self.num_loop):
                self.out_[i] = 1

    mod = Mod(4)
    src = verilog(mod)["mod"]
    assert "out[2'(i)] = 1'h1;" in src


def test_switch(check_gold):
    class Switch(Generator):
        def __init__(self):
            super().__init__("switch_test")

            self._in = self.port("in", 3, PortDirection.In)
            self._out = self.port("out", 3, PortDirection.Out)

            self.add_always(self.logic)

        @always_comb
        def logic(self):
            if self._in == const(0, 3):
                self._out = 0
            elif self._in == const(1, 3):
                self._out = 1
            else:
                self._out = 2

    mod = Switch()
    check_gold(mod, "test_switch")


def test_pass_through(check_gold):
    mod = PassThroughTop()
    # turn off pass through module optimization since it will remove
    # mod2 completely
    check_gold(mod, "test_pass_through", optimize_passthrough=True)


def test_nested_if(check_gold):
    class Mod(Generator):
        def __init__(self):
            super().__init__("mod1")
            self.in_ = self.port("in", 2, PortDirection.In)
            self.out_ = self.port("out", 2, PortDirection.Out)

            self.add_always(self.nested_if)

        @always_comb
        def nested_if(self):
            if self.in_ < const(1, 2):
                if self.in_ < const(2, 2):
                    self.out_ = 1
                else:
                    self.out_ = 3
            else:
                self.out_ = 2

    mod = Mod()
    check_gold(mod, "test_nested_if")


def test_fanout_mod_inst(check_gold):
    class Mod2(Generator):
        def __init__(self):
            super().__init__("mod2")
            self.in_ = self.port("in", 1, PortDirection.In)
            self.out_ = self.port("out", 1, PortDirection.Out)

            self.mod_1 = PassThroughMod()
            self.mod_2 = PassThroughMod()

            self.add_child("mod1", self.mod_1)
            self.add_child("mod3", self.mod_2)

            self.wire(self.in_, self.mod_1.in_)
            self.wire(self.in_, self.mod_2.in_)

            self.add_always(self.code)

        @always_comb
        def code(self):
            self.out_ = self.mod_1.out_ + self.mod_2.out_

    mod = Mod2()
    check_gold(mod, "test_fanout_mod_inst", optimize_passthrough=False)
    Generator.clear_context()
    mod2 = Mod2()
    check_gold(mod2, "test_fanout_mod_inst_passthrough")


def test_debug():
    class Mod(Generator):
        def __init__(self):
            super().__init__("mod1", True)
            self.in_ = self.port("in", 1, PortDirection.In)
            self.out_1 = self.port("out1", 1, PortDirection.Out)
            self.out_2 = self.port("out2", 1, PortDirection.Out)

            self.wire(self.out_1, self.in_)

            self.add_always(self.code)

        @always_comb
        def code(self):
            self.out_2 = self.in_

    mod = Mod()
    mod_src, mod_debug = verilog(mod, debug_fn_ln=True)
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

            self.add_always(self.code)

        @always_comb
        def code(self):
            if self.in_ == const(1, 1):
                self.out_ = const(1, 4)
            else:
                self.out_ = const(100, 10)

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

            self.add_always(self.code)

        @always_ff((posedge, "clk"))
        def code(self):
            self.out_ = 1

    try:
        mod = Mod()
        verilog(mod)
        assert False
    except StmtException as ex:
        print(ex)
        assert True


def test_data_if(check_gold):
    class Mod(Generator):
        def __init__(self, bool_flag):
            super().__init__("mod1")
            self.in_ = self.port("in", 1, PortDirection.In)
            self.out_ = self.port("out", 1, PortDirection.Out)
            self.bool_flag = bool_flag

            self.add_always(self.code)

        @always_comb
        def code(self):
            if self.bool_flag:
                if self.in_ == const(1, 1):
                    self.out_ = 1
                else:
                    self.out_ = 0
            else:
                if self.in_ == const(0, 1):
                    self.out_ = 0
                else:
                    self.out_ = 1

    mod = Mod(True)
    check_gold(mod, "test_data_if_true")
    # need to clear the context, otherwise it will be a different module name
    Generator.clear_context()
    mod = Mod(False)
    check_gold(mod, "test_data_if_false")


def test_static_eval_for_loop(check_gold):
    class Mod(Generator):
        def __init__(self, num_loop):
            super().__init__("mod1", True)
            self.in_ = self.port("in", 1, PortDirection.In)
            self.out_ = self.port("out", num_loop, PortDirection.Out)
            self.num_loop = num_loop

            self.add_always(self.code)

        @always_comb
        def code(self):
            if self.in_ == const(1, 1):
                for i in range(self.num_loop):
                    self.out_[i] = 1
            else:
                for i in range(self.num_loop):
                    self.out_[i] = 0

    loop = 4
    mod = Mod(loop)
    mod_src, mod_debug = verilog(mod, debug_fn_ln=True)
    mod_mapping = mod_debug["mod1"]
    lines = list(mod_mapping.keys())
    lines.sort()
    for ii in range(len(mod_mapping) - loop, len(mod_mapping) - 1):
        assert mod_mapping[lines[-1]][-1] == mod_mapping[lines[ii]][-1]
    Generator.clear_context()
    check_gold(mod, "test_static_eval_for_loop")


def test_const_port(check_gold):
    class Mod(Generator):
        def __init__(self):
            super().__init__("mod")

            self.in_ = self.port("in", 1, PortDirection.In)
            self.out_ = self.port("out", 2, PortDirection.Out)

            self.child = PassThroughMod()
            self.add_child("child", self.child)
            self.wire(self.child.in_, const(0, 1))
            self.wire(self.out_[0], self.child.out_)
            self.wire(self.out_[1], self.in_)

    mod = Mod()
    check_gold(mod, "test_const_port", optimize_passthrough=False)


def test_create(check_gold):
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
    assert mod3.def_instance == mod1

    # modify mod 3
    mod3.initialize_clone()
    mod3.in_.width = 3
    mod3.out_.width = 3
    assert not mod3.is_cloned
    check_gold(mod3, "test_create")


@pytest.mark.skipif(no_verilator, reason="verilator not available")
def test_clone():
    class Mod2(Generator):
        def __init__(self):
            super().__init__("mod2")
            self.in_ = self.input("in", 2)
            self.out_ = self.output("out", 2)

            self.child1 = PassThroughMod.clone()
            self.child2 = PassThroughMod.clone()
            self.add_child("child1", self.child1)
            self.add_child("child2", self.child2)

            self.add_always(self.code)

        @always_comb
        def code(self):
            self.child1.ports["in"] = self.in_[0]
            self.child2.ports["in"] = self.in_[1]

            self.out_[0] = self.child1.ports.out
            self.out_[1] = self.child2.ports.out

    mod = Mod2()
    assert not mod.child1.is_cloned
    assert mod.child2.is_cloned
    mod_src = verilog(mod, optimize_fanout=False, optimize_passthrough=False)
    assert is_valid_verilog(mod_src)


def test_packed_struct(check_gold, check_file):
    struct = PackedStruct("config_data", [("read", 16),
                                          ("data", 16)])

    class Mod(Generator):
        def __init__(self, debug=False):
            super().__init__("mod", debug=debug)
            self.input("in", struct)
            self.output("out", struct)
            v = self.var_packed("v", struct)
            self.wire(self.ports["out"], self.ports["in"])
            self.wire(v, self.ports["in"])

            # tests
            # assert v.width == 16 + 16
            assert "read" in v.member_names()
            assert "data" in v.member_names()
            assert v["read"].width == 16

    mod = Mod()
    check_gold(mod, "test_packed_struct", optimize_passthrough=False)
    Generator.clear_context()
    mod = Mod(True)
    mod.name = "packed_struct"
    with tempfile.TemporaryDirectory() as temp:
        verilog(mod, output_dir=temp, debug_fn_ln=True)
        mod_file = os.path.join(temp, "packed_struct.sv")
        def_file = os.path.join(temp, "packed_struct_pkg.svh")
        import json
        # json is correct
        if is_windows:
            pytest.skip("Windows new line problem")
        with open(os.path.join(temp, "packed_struct.sv.debug")) as f:
            json.load(f)
        check_file(mod_file, "packed_struct_pkg.sv")
        check_file(def_file, "packed_struct_pkg.svh")


@pytest.mark.skipif(no_verilator, reason="verilator not available")
def test_more_debug1():
    mod = PassThroughTop()
    mod_src, debug_info = verilog(mod, debug_fn_ln=True)
    debug = debug_info["top"]
    assert is_valid_verilog(mod_src)
    assert len(debug) > 3


@pytest.mark.skipif(no_verilator, reason="verilator not available")
def test_more_debug2():
    class Top(Generator):
        def __init__(self):
            super().__init__("top", True)

            self.port("in", 1, PortDirection.In)
            self.port("out", 1, PortDirection.Out)

            pass_through = PassThroughMod()
            self.add_child("pass", pass_through)
            self.wire(self["pass"].ports["in"], self.ports["in"], )

            self.add_always(self.code_block)

        @always_comb
        def code_block(self):
            self.ports.out = self["pass"].ports.out

    mod = Top()
    mod_src, debug_info = verilog(mod, debug_fn_ln=True)
    debug = debug_info["top"]
    assert is_valid_verilog(mod_src)
    assert len(debug) > 3


@pytest.mark.skipif(no_verilator, reason="verilator not available")
def test_verilog_file():
    mod = PassThroughTop()
    with tempfile.TemporaryDirectory() as tempdir:
        filename = os.path.join(tempdir, "mod.sv")
        verilog(mod, filename=filename, debug_fn_ln=True, optimize_passthrough=False)
        with open(filename) as f:
            src = f.read()
            assert is_valid_verilog(src)


def test_wire_merge(check_gold):
    class TestModule(Generator):
        def __init__(self, width):
            super().__init__("Test")
            self.port("in", width, PortDirection.In)
            self.port("out", width, PortDirection.Out)

            for i in range(width):
                self.wire(self.ports["out"][i], self.ports["in"][i])

    mod = TestModule(4)
    check_gold(mod, "test_wire_merge")


def test_remove_child():
    top = PassThroughTop()
    child = top["pass"]
    assert child in top
    top.remove_child_generator(child)
    assert child not in top
    # top should be empty now
    assert top.stmts_count == 0


@pytest.mark.skipif(no_verilator, reason="verilator not available")
def test_syntax_sugar():
    mod = Generator("mod", debug=True)
    out_ = mod.output("out", 1)
    in_ = mod.input("in", 1)
    comb = mod.combinational()
    comb.if_(in_ == 1).then_(out_(0)).else_(out_(1))

    mod_src = verilog(mod)
    is_valid_verilog(mod_src)

    Generator.clear_context()
    mod = Generator("mod", debug=True)
    out_ = mod.output("out", 1)
    in_ = mod.input("in", 1)
    comb = mod.combinational()
    comb.switch_(in_).case_(1, out_(1)).case_(0, out_(0))

    mod_src = verilog(mod)
    is_valid_verilog(mod_src)


@pytest.mark.skipif(no_verilator, reason="verilator not available")
def test_zero_ext():
    mod = Generator("mod", debug=True)
    out_ = mod.port("out", 2, PortDirection.Out)
    in_ = mod.port("in", 1, PortDirection.In)
    mod.wire(out_, ext(in_, 2))

    mod_src = verilog(mod)
    is_valid_verilog(mod_src)


def test_port_array(check_gold):
    mod = Generator("mod", True)
    in_ = mod.port("in", 2, PortDirection.In, size=2)
    out1 = mod.port("out1", 2, PortDirection.Out, size=2)
    out2 = mod.port("out2", 2, PortDirection.Out, size=2)
    mod.wire(out1, in_)
    mod.wire(out2[0][0], in_[0][1])
    mod.wire(out2[0][1], in_[0][0])
    mod.wire(out2[1], in_[1])

    check_gold(mod, "test_port_array")


def test_simple_pipeline(check_gold):
    mod = PassThroughMod()
    # add a clock
    mod.clock("clk")
    attr = Attribute()
    attr.type_str = "pipeline"
    attr.value_str = "2"
    mod.add_attribute(attr)

    check_gold(mod, "test_simple_pipeline", insert_pipeline_stages=True)


def test_replace(check_gold):
    mod = PassThroughTop()

    class Mod(Generator):
        def __init__(self):
            super().__init__("test", True)
            self.in_ = self.input("in", 1)
            self.out_ = self.output("out", 1)
            self.wire(self.out_, self.in_)

    child = Mod()
    mod.replace("pass", child)
    check_gold(mod, "test_replace", optimize_passthrough=False)


def test_local_function(check_gold):
    class Mod(Generator):
        def __init__(self):
            super().__init__("test")
            in_ = self.input("in", 1)
            out_ = self.output("out", 1)
            clk = self.clock("clk")

            @always_ff((posedge, "clk"))
            def code_block():
                if clk:
                    out_ = in_

            self.add_always(code_block)

    mod = Mod()
    check_gold(mod, "test_local_function")


def test_reg_next(check_gold):
    class Mod(Generator):
        def __init__(self):
            super().__init__("test")
            in_ = self.input("in", 1)
            out_ = self.output("out", 1)
            try:
                a = self.reg_next("var1", in_)
                assert False
            except AssertionError:
                assert True
            # add a clock
            self.clock("clk")
            a = self.reg_next("a", in_)
            b = self.reg_next("b", a)
            self.wire(out_, b)

    mod = Mod()
    check_gold(mod, "test_reg_next")


def test_reg_init(check_gold):
    class Mod(Generator):
        def __init__(self):
            super().__init__("test")
            in_ = self.input("in", 1)
            out_ = self.output("out", 1)
            # add a clock
            self.clock("clk")
            # add a reset
            self.reset("rst")
            a = self.reg_init("a", in_)
            b = self.reg_init("b", a)
            self.wire(out_, b)

    mod = Mod()
    check_gold(mod, "test_reg_init")


def test_reg_enable(check_gold):
    class Mod(Generator):
        def __init__(self):
            super().__init__("test")
            in_ = self.input("in", 1)
            en_ = self.input("en", 1)
            out_ = self.output("out", 1)
            # add a clock
            self.clock("clk")
            a = self.reg_enable("a", in_, en_)
            b = self.reg_enable("b", a, en_)
            self.wire(out_, b)

    mod = Mod()
    check_gold(mod, "test_reg_enable")


def test_ternary(check_gold):
    from kratos import mux

    class Mod(Generator):
        def __init__(self):
            super().__init__("test")
            in1 = self.input("in1", 1)
            in2 = self.input("in2", 1)
            in3 = self.input("in3", 1)
            out = self.output("out", 1)

            self.wire(out, mux(in1, in2, in3))

    mod = Mod()
    check_gold(mod, "test_ternary")


def test_bundle(check_gold):
    class Test(PortBundle):
        def __init__(self):
            super().__init__(True)
            self.input("a", 1)
            self.output("b", 1)

    class Mod(Generator):
        def __init__(self):
            super().__init__("test_bundle", True)

            p = self.port_bundle("in_port", Test())
            self.port_bundle("out_port", Test().flip())

            self.wire(p.a, self.ports.out_port.a)
            self.wire(self.ports.in_port.b, self.ports.out_port.b)

    mod = Mod()
    check_gold(mod, "test_bundle")


def test_bundle_pack():
    class Test(PortBundle):
        def __init__(self):
            super().__init__(True)
            self.input("a", 1)
            self.input("b", 1)

    class Mod1(Generator):
        def __init__(self):
            super().__init__("mod1")

            p = self.port_bundle("p", Test())
            self.p = p
            self.a = self.output("a", 1)
            self.b = self.output("b", 1)
            self.wire(self.a, p["a"])
            self.wire(self.b, p["b"])

    class Mod2(Generator):
        def __init__(self):
            super().__init__("mod2")

            p = self.port_bundle("p", Test().flip())
            self.p = p
            self.a = self.input("a", 1)
            self.b = self.input("b", 1)
            self.wire(p["a"], self.a)
            self.wire(p["b"], self.b)

    class Mod(Generator):
        def __init__(self):
            super().__init__("mod")
            in_ = self.input("a", 1)
            out_ = self.output("b", 1)
            mod1 = Mod1()
            mod2 = Mod2()

            self.add_child("m1", mod1)
            self.add_child("m2", mod2)

            self.wire(mod1.p.a, in_)
            self.wire(mod1.p.b, in_)
            self.wire(mod2.a, in_)
            self.wire(mod2.b, in_)
            self.add_stmt(out_.assign(mod1.a + mod2.p.a))

    mod = Mod()
    mod_src = verilog(mod, optimize_passthrough=False)
    # assert is_valid_verilog(mod_src)


def test_named_block(check_gold):
    mod = Generator("mod", debug=True)
    out_ = mod.output("out", 1)
    in_ = mod.port("in", 1, PortDirection.In)
    comb = mod.combinational()
    if_ = comb.if_(in_ == 1)
    if_.then_(out_(0)).else_(out_(1))
    mod.mark_stmt("TEST", if_.then_body())

    @always_comb
    def code():
        out_ = 1

    mod.add_always(code, label="TEST2")

    check_gold(mod, "test_named_block", check_multiple_driver=False)


def test_enum(check_gold):
    mod = Generator("mod", debug=True)
    out_ = mod.output("out", 1)
    in_ = mod.input("in", 1)
    mod.enum("color", {"red": 1, "green": 2}, 2)
    mod.wire(out_, in_)

    check_gold(mod, "test_enum")


def setup_fsm(fsm, out_, in_):
    # add outputs
    fsm.output(out_)
    # add states
    red = fsm.add_state("Red")
    blue = fsm.add_state("Blue")
    # set the state transition
    red.next(red, in_ == 0)
    red.next(blue, in_ == 1)
    blue.next(red, in_ == 1)
    # fill in outputs
    red.output(out_, 2)
    blue.output(out_, 1)
    # set the start case
    fsm.set_start_state("Red")


def test_fsm(check_gold, check_file):
    mod = Generator("mod", debug=True)
    out_ = mod.output("out", 2)
    in_ = mod.input("in", 2)
    # fsm requires a clk and async rst
    mod.clock("clk")
    mod.reset("rst")
    # add a dummy fsm
    fsm = mod.add_fsm("Color")
    # setup FSM
    setup_fsm(fsm, out_, in_)

    check_gold(mod, "test_fsm", optimize_if=False)
    # output fsm graph
    dot = fsm.dot_graph()
    check_file(dot, "test_fsm.dot")
    csv = fsm.output_table()
    check_file(csv, "test_fsm.csv")


def test_fsm_mealy(check_gold):
    mod = Generator("mod", debug=True)
    out_ = mod.output("out", 2)
    in_ = mod.input("in", 2)
    # fsm requires a clk and async rst
    mod.clock("clk")
    mod.reset("rst")
    # add a dummy fsm
    fsm = mod.add_fsm("Color")
    # setup FSM
    setup_fsm(fsm, out_, in_)
    # use mealy
    fsm.is_moore = False
    check_gold(mod, "test_fsm_mealy", optimize_if=False)


def test_function(check_gold):
    from kratos.func import function

    class Mod(Generator):
        def __init__(self):
            super().__init__("mod", debug=True)
            self._in = self.input("in", 2)
            self._out = self.output("out", 2)
            self._out2 = self.output("out2", 2)

            self.add_always(self.code)

        @function
        def update_out(self, value, predicate):
            self._out2 = value
            if predicate:
                return value + self._in
            else:
                return value

        @always_comb
        def code(self):
            # because the types are inferred
            # implicit const conversion doesn't work here
            self._out = self.update_out(self._in, const(1, 1))

    mod = Mod()
    check_gold(mod, "test_function")


def test_function_missing_return():
    from kratos.func import function

    class Mod(Generator):
        def __init__(self):
            super().__init__("mod", debug=True)
            self._in = self.input("in", 2)
            self._out = self.output("out", 2)

            self.add_always(self.code)

        @function
        def update_out(self, value, predicate):
            self._out = value
            if predicate:
                return value + self._in

        @always_comb
        def code(self):
            # because the types are inferred
            # implicit const conversion doesn't work here
            self._out = self.update_out(self._in, const(1, 1))

    mod = Mod()
    try:
        verilog(mod)
        assert False
    except StmtException:
        assert True


def test_reg_file(check_gold):
    class Mod(Generator):
        def __init__(self):
            super().__init__("mod")
            self._in = self.input("in", 4)
            self._out = self.output("out", 4)
            self.waddr = self.input("warr", 2)
            self.raddr = self.input("raddr", 2)
            self.reg = self.var("reg_file", 4, size=4)

            self.add_always(self.code)

        @always_comb
        def code(self):
            self.reg[self.waddr] = self._in
            self._out = self.reg[self.raddr]

    mod = Mod()
    check_gold(mod, "test_reg_file")


def test_comment(check_gold):
    class Mod(Generator):
        def __init__(self):
            super().__init__("mod")
            self._in = self.input("in", 1)
            self._out = self.output("out", 1)
            self._out2 = self.output("out2", 1)
            self._out3 = self.output("out3", 1)
            self.var = self.var("v", 1)

            child = PassThroughMod()
            self.add_child("child", child, "This is a comment")
            self.wire(self._in, child.in_)
            self.wire(self._out, child.out_)
            self.wire(self._out2, self.var)

            self._in.comment = "Input port"
            self.var.comment = "variable comment"
            self.add_always(self.code)

        @always_comb
        def code(self):
            comment("Another comment")
            self._out3 = self._in

    mod = Mod()
    check_gold(mod, "test_comment", optimize_passthrough=False)


def test_packed_array(check_gold):
    class Mod(Generator):
        def __init__(self):
            super().__init__("mod")
            self._in = self.input("in", 4, size=6, packed=True)
            self._out = self.output("out", 4, size=6, packed=True)
            self.wire(self._in, self._out)

    mod = Mod()
    check_gold(mod, "test_packed_array")


def test_rename():
    mod = PassThroughTop()
    child = mod["pass"]
    child.instance_name = "test"
    assert child == mod["test"]
    assert mod.internal_generator.has_child_generator("test")
    child.name = "test2"
    assert mod["test"].internal_generator.name == "test2"


def test_c_dpi_function(check_gold):
    from kratos.func import dpi_function

    @dpi_function(8)
    def add(arg0, arg1):
        pass

    class Mod(Generator):
        def __init__(self):
            super().__init__("mod", debug=True)
            self._in = self.input("in", 2)
            self._out = self.output("out", 8)

            self.add_always(self.code)

        @always_comb
        def code(self):
            # because the types are inferred
            # implicit const conversion doesn't work here
            self._out = add(self._in, const(1, 2))

    mod = Mod()
    # once it's turned off, user has to handle sv logic themselves in the
    # c interface
    check_gold(mod, "test_dpi", int_dpi_interface=False)


def test_nested_fsm(check_gold, check_file):
    mod = Generator("mod", debug=True)
    out_ = mod.output("out", 2)
    in_ = mod.input("in", 2)
    # fsm requires a clk and async rst
    mod.clock("clk")
    mod.reset("rst")
    # add a dummy fsm
    fsm = mod.add_fsm("Color")
    setup_fsm(fsm, out_, in_)
    second_fsm = mod.add_fsm("HSV")
    fsm.add_child_fsm(second_fsm)
    idle = second_fsm.add_state("idle")
    idle.next(fsm["Red"], in_ == 0)
    fsm["Red"].next(idle, in_ == 2)
    second_fsm.output(out_)
    idle.output(out_, 2)

    dot = fsm.dot_graph()
    check_file(dot, "test_nested_fsm.dot")
    check_gold(mod, "test_nested_fsm", optimize_if=False)


def test_symbol_table():
    from kratos.debug import extract_symbol_table
    mod = AsyncReg(16, True)
    verilog(mod)
    table, _ = extract_symbol_table(mod)
    assert len(table) == 1
    assert len(table[mod]) == 5


def test_cast():
    from kratos.util import clock, clock_en

    class Mod1(Generator):
        def __init__(self):
            super().__init__("mod")
            self.v = self.var("v", 1)
            self.out = self.output("out", 1)
            self.add_always(self.code)

        @always_ff((posedge, "v"))
        def code(self):
            self.out = 1

    mod = Mod1()
    try:
        verilog(mod)
        assert False
    except StmtException:
        assert True

    class Mod2(Generator):
        def __init__(self):
            super().__init__("mod")
            self.v = self.var("v", 1)
            clk = clock(self.v)
            cn_var = self.var("cn", 1)
            cn = self.output("cn_out", 1, PortType.ClockEnable)
            self.add_stmt(cn.assign(clock_en(cn_var)))
            # only procedural allowed
            seq = self.sequential((posedge, clock(self.v)))
            seq.add_stmt(self.output("out", 1).assign(const(1, 1)))

            @always_ff((posedge, clk))
            def fn():
                self.v = 1

            self.add_always(fn)

    mod = Mod2()
    verilog(mod)


def test_async_no_latch():
    class Mod(Generator):
        def __init__(self):
            super().__init__("mod", True)
            clk = self.clock("clk")
            rst = self.reset("rst")
            cen = self.input("cen", 1, PortType.ClockEnable)
            in_ = self.input("in", 1)
            out_ = self.output("out", 1)

            @always_ff((posedge, "clk"), (posedge, "rst"))
            def code():
                if rst:
                    out_ = 0
                elif cen:
                    out_ = in_

            self.add_always(code)

    mod = Mod()
    verilog(mod)


def test_async_latch():
    class Mod(Generator):
        def __init__(self):
            super().__init__("mod", True)
            clk = self.clock("clk")
            rst = self.reset("rst")
            cen = self.input("cen", 1, PortType.ClockEnable)
            in_ = self.input("in", 1)
            out_ = self.output("out", 1)

            @always_ff((posedge, "clk"), (posedge, "rst"))
            def code():
                if rst:
                    out_ = 0

            self.add_always(code)

    mod = Mod()
    try:
        verilog(mod)
        assert False
    except StmtException:
        assert True


def test_param(check_gold):
    mod = Generator("mod", True)
    param = mod.parameter("P", 4, 4)
    param2 = mod.parameter("P2", 4, 4)
    param3 = mod.parameter("P3", 4)  # P3 doesn't have init or value
    in_ = mod.input("in", param)
    out = mod.output("out", param2)
    var = mod.var("v", param)
    mod.wire(var, in_)
    mod.wire(out, var * 2)

    check_gold(mod, "test_param")
    param.value = 2
    try:
        verilog(mod)
        assert False
    except VarException:
        assert True
    param.value = 4
    verilog(mod)


def test_nested_param(check_gold):
    parent = Generator("parent")
    param1 = parent.parameter("P", 4, 4)
    # use normal variable to see how decoupling works
    in1 = parent.var("in", param1)
    out1 = parent.var("out", param1)

    child = Generator("child")
    param2 = child.parameter("P2", 4, 4)
    in2 = child.input("in", param2)
    out2 = child.output("out", param2)
    child.wire(out2, in2)

    parent.add_child("mod", child)
    parent.wire(in1, in2)
    parent.wire(out1, out2)

    # change the value
    param2.value = param1
    # test the value propagation
    param1.value = 2
    check_gold(parent, "test_nested_param", optimize_passthrough=False)


def hash_param_width():
    class Mod(Generator):
        def __init__(self, value):
            super().__init__("mod")
            p = self.parameter("P", 2, 2)
            out = self.output("out", p)
            self.wire(out, p)
            p.value = value

    mod1 = Mod(1)
    mod2 = Mod(2)
    parent = Generator("parent")
    parent.add_child("mod1", mod1)
    parent.add_child("mod2", mod2)

    hash_generators_parallel(parent.internal_generator)
    c = Generator.get_context()
    hash1 = c.get_hash(mod1.internal_generator)
    hash2 = c.get_hash(mod2.internal_generator)
    assert hash1 == hash2


def test_long_statement(check_gold):
    from kratos import concat
    mod = Generator("mod")
    a = mod.input("this_is_a_long_name", 1)
    num_concat = 6
    b = mod.output("out", num_concat)
    mod.wire(b, concat(*[a for _ in range(num_concat)]))
    check_gold(mod, "test_long_statement")


def test_create_stub(check_file):
    from kratos import create_stub
    mod = Generator("mod")
    mod.input("a", 16, size=16)
    mod.output("b", 1)
    mod.input("c", 16)
    mod.var("d", 1)  # this should not be generated
    check_file(create_stub(mod), "test_create_stub.sv")


def test_fsm_state(check_gold):
    from kratos import negedge
    mod = Generator("mod", debug=True)
    out_ = mod.output("out", 2)
    in_ = mod.input("in", 2)
    # fsm requires a clk and async rst
    clk = mod.clock("clk")
    rst = mod.reset("rst")
    # add a dummy fsm
    fsm = mod.add_fsm("Color", reset_high=False)
    # setup FSM
    setup_fsm(fsm, out_, in_)
    # realize fsm now
    fsm.realize()
    current_state = fsm.current_state
    # create an enum var based on current_state
    state_enum = current_state.enum_type()
    # can create a variable from the enum definition
    # notice that variable s will be optimized away if not used
    s = mod.enum_var("s", state_enum)
    c = mod.var("counter", 1)

    @always_ff((posedge, clk), (negedge, rst))
    def counter():
        if rst.r_not():
            c = 0
        elif current_state == state_enum.Red:
            c = c + 1

    mod.add_always(counter)
    check_gold(mod, "test_fsm_state", optimize_if=False)


def test_not_if(check_gold):
    mod = Generator("mod")
    a = mod.output("a", 1)
    clk = mod.clock("clk")
    rst = mod.reset("rst", is_async=False)  # synchronous reset

    @always_ff((posedge, clk))
    def code():
        if not rst:
            a = 1
        else:
            a = 0

    mod.add_always(code)
    check_gold(mod, "test_not_if")


def test_exception(check_gold):
    mod = Generator("mod", True)
    in_ = mod.input("in", 1)

    @always_comb
    def code():
        if in_ == 1:
            raise Exception()

    mod.add_always(code)
    check_gold(mod, "test_exception")


def test_enum_port(check_gold):
    from kratos import enum, has_enum
    mod = Generator("mod")
    enum_ = enum("State", ["IDLE", "WAIT", "WORK"])
    assert has_enum("State")
    in_ = mod.input("in", enum_)
    out = mod.output("out", enum_)
    mod.wire(out, in_)
    check_gold(mod, "test_enum_port")
    Generator.clear_context()
    mod = Generator("mod")
    enum_ = enum("State", [("IDLE", 0), ("WAIT", 1), ("WORK", 2)])
    in_ = mod.input("in", enum_)
    out = mod.output("out", enum_)
    mod.wire(out, in_)
    check_gold(mod, "test_enum_port")


def test_interface_modport_local(check_gold):
    from kratos import Interface
    mod = Generator("mod")

    class ConfigInterface(Interface):
        def __init__(self):
            Interface.__init__(self, "Config")
            self.var("read", 1, 1)
            self.var("write", 1, 1)
            # create modport
            self.slave = self.modport("Slave")
            self.slave.set_input("read")
            self.slave.set_output("write")

    interface = ConfigInterface()
    i1 = mod.interface(interface, "bus")
    child = Generator("child")
    mod.add_child("child", child)
    # set it to True for port interface
    child_bus = child.interface(interface.slave, "bus_s", True)
    # child logic with the interface ports
    child.wire(child_bus.write, child_bus.read)
    # wire the parent to child
    mod.wire(i1.Slave, child_bus)

    check_gold(mod, "test_interface_modport_local", optimize_passthrough=False)


def test_interface_port_wiring(check_gold):
    from kratos import Interface
    mod = Generator("mod")

    class ConfigInterface(Interface):
        def __init__(self):
            Interface.__init__(self, "Config")
            self.input("read", 1, 1)
            self.output("write", 1, 1)

    interface = ConfigInterface()
    i1 = mod.interface(interface, "bus")
    # wire local variables to the interface
    read = mod.var("read", 1)
    write = mod.var("write", 1)
    mod.wire(i1.read, read)
    mod.wire(write, i1.write)

    # create child module and use the interface as port
    child = Generator("child")
    mod.add_child("child", child)
    i2 = child.interface(interface, "bus2", True)
    child.wire(i2.write, i2.read)

    # wire the interface
    mod.wire(i1, i2)
    check_gold(mod, "test_interface_port_wiring", optimize_passthrough=False)


def test_track_generated_definition():
    mod = PassThroughMod()
    with tempfile.TemporaryDirectory() as tempdir:
        filename = os.path.join(tempdir, "test.sv")
        verilog(mod, filename=filename, track_generated_definition=True)
        t1 = os.path.getmtime(filename)
        verilog(mod, filename=filename, track_generated_definition=True)
        with open(filename) as f:
            content = f.read()
        assert content == ""  # empty since no content is generated


def test_call_always():
    @always_comb
    def code():
        pass

    try:
        code()
        assert False
    except SyntaxError:
        assert True


def test_wrapper_flatten_generator(check_gold):
    mod = Generator("mod")
    a = mod.input("a", 4, size=[3, 2])
    b = mod.output("b", 4, size=[3, 2])
    attr = kratos.Attribute()
    attr.value_str = "a"
    a.add_attribute(attr)
    mod.wire(a, b)
    from _kratos import create_wrapper_flatten
    wrapper = create_wrapper_flatten(mod.internal_generator, "wrapper")
    wrapper = Generator(wrapper.name, internal_generator=wrapper)
    check_gold(wrapper, gold_name="test_wrapper_flatten_generator",
               optimize_passthrough=False)
    a_0_0 = wrapper.ports.a_0_0
    attrs = a_0_0.find_attribute(lambda x: x.value_str == "a")
    assert len(attrs) == 1


def test_register_extraction():
    mod = Generator("mod")
    a = mod.input("a", 4)
    b = mod.output("b", 4)
    rst = mod.reset("rst")
    clk = mod.clock("clk")

    @always_ff((posedge, "clk"), (posedge, "rst"))
    def code():
        if rst:
            b = 0
        else:
            b = a + b

    mod.add_always(code)

    import _kratos
    regs = _kratos.passes.extract_register_names(mod.internal_generator)
    assert len(regs) == 1
    assert "mod.b" in regs


def test_iadd_transform():
    mod = Generator("mod", True)
    a = mod.var("a", 4)
    clk = mod.clock("clk")

    @always_ff((posedge, clk))
    def code():
        a += 1

    mod.add_always(code)
    src = verilog(mod)
    assert "a <= a + 4'h1;" in src["mod"]
    # make sure the line info gets passed down
    stmt = mod.get_stmt_by_index(0)[0]
    assert len(stmt.fn_name_ln) == 1


def test_if_logical_cond():
    mod = Generator("mod")
    a = mod.var("a", 1)
    b = mod.var("b", 1)
    c = mod.var("c", 1)

    @always_comb
    def code():
        if (not a and b) or a:
            c = 1
        else:
            c = 0

    mod.add_always(code)

    @always_comb
    def illegal():
        if 1 and a:
            c = 1

    # test illegal
    try:
        mod.add_always(illegal)
        assert False
    except SyntaxError:
        assert True


def test_wiring_with_instantiation():
    mod = Generator("parent")
    child = Generator("child")
    a = mod.var("a", 1)
    mod.var("b", 1)
    mod.output("c", 1)
    child_in = child.input("in_port", 1)
    child_out1 = child.output("out_port1", 1)
    child_out2 = child.output("out_port2", 1)
    child.wire(child_out1, child_in)
    child.wire(child_out2, child_in)
    # we use the port name to instantiate the connection
    # due to Python's limitation, we can use keyword such as "in"
    # the syntax is child_port_name=parent_port
    # where parent port can be either port name or port variable
    mod.add_child("child_inst", child,
                  in_port=a, out_port1="b", out_port2="c")
    r = verilog(mod)
    assert ".out_port1(b)" in r["parent"]


def test_nested_loop():
    mod = Generator("mod")
    a = mod.var("a", 8)

    @always_comb
    def code():
        for i in range(2):
            a[i] = i
            for j in range(4):
                a[i * 4 + j] = 1

    mod.add_always(code)
    src = verilog(mod)["mod"]
    assert "a[3'(i)] = 1'(i);" in src
    assert "a[(3'(i) * 3'h4) + 3'(j)] = 1'h1;" in src
    # with debug on
    mod = Generator("mod", True)
    a = mod.var("a", 8)
    mod.add_always(code)
    src = verilog(mod)["mod"]
    assert "a[7] = 1'h1;" in src


def test_turn_off_optimization():
    class Mod(Generator):
        def __init__(self, merge):
            super().__init__("mod")
            a = self.var("a", 2)
            b = self.var("b", 2)
            c = self.var("c", 2)
            clk = self.clock("clk")

            @always_ff((posedge, clk))
            def code():
                if a == 0:
                    b = 0
                # NOTE: this is not synthesizable verilog!
                if a == 1:
                    c = 1

            self.add_always(code, merge_if_block=merge)
    src = verilog(Mod(False), check_flip_flop_always_ff=False)["mod"]
    assert "  if (a == 2'h1) begin" in src
    assert "else if" not in src
    src = verilog(Mod(True))["mod"]
    assert "else if" in src


def test_generator_property(check_gold):
    from kratos import Sequence
    mod = Generator("mod")
    a = mod.input("a", 1)
    a_tmp = mod.var("a_tmp", 1)
    b = mod.output("b", 1)
    # any sequence-based property needs a clock
    clk = mod.clock("clk")

    @always_ff((posedge, clk))
    def code():
        if (a == 1) & ~a_tmp:
            b = 0
            a_tmp = 1
        elif a_tmp:
            b = 1

    mod.add_code(code)

    seq = Sequence(a == 1)
    # if a == 1, then it imply b == 0, and the next cycle, b == 1
    seq.imply(b == 0).wait(1).imply(b == 1)
    # add this sequence to the generator
    p1 = mod.property("rule1", seq)
    p1.action = kratos.PropertyAction.Assert

    p2 = mod.property("rule2", seq)
    p2.action = kratos.PropertyAction.Assume

    p3 = mod.property("rule3", seq)
    p3.action = kratos.PropertyAction.Cover

    check_gold(mod, gold_name="test_generator_property")


def test_verilog_ln_fix():
    from kratos.func import dpi_function

    @dpi_function(8)
    def add(arg0, arg1):
        pass

    class Mod(Generator):
        def __init__(self):
            super().__init__("mod", debug=True)
            self._in = self.input("in", 2)
            self._out = self.output("out", 8)
            self.add_always(self.code)

        @always_comb
        def code(self):
            self._out = add(self._in, const(1, 2))
            if self._in == 0:
                self._out = 1

    mod = Mod()
    with tempfile.TemporaryDirectory() as temp:
        filename = os.path.join(temp, "test.sv")
        src = verilog(mod, filename=filename)[0]
        content = src["mod"]

    mod_i = mod.internal_generator
    assert mod_i.verilog_ln == 2
    lines = content.split("\n")
    stmt_0 = min([i for i in range(len(lines)) if "add (" in lines[i]])
    stmt_1 = min([i for i in range(len(lines)) if "if" in lines[i]])
    # + 1 for using starting-1 line number format
    # another + 1 for DPI header offset
    assert mod.get_stmt_by_index(0)[0].verilog_ln == stmt_0 + 1 + 1
    assert mod.get_stmt_by_index(0)[1].then_body().verilog_ln == stmt_1 + 2


def transform_block_comment():
    mod = Generator("mod")

    @always_comb
    def code():
        """
        this is comment
        this is another comment
        """

    mod.add_always(code)
    src = verilog(mod)["mod"]
    assert "this is comment" in src
    assert "this is another comment" in src


def test_add_only():
    # this is for testing internal public API, advanced user only
    parent = Generator("parent")
    child = Generator("child")
    parent.add_child(child.instance_name, child, python_only=True)
    assert child not in parent


def test_always_parameter():
    mod = Generator("mod")
    a = mod.output("a", 3)

    @always_comb
    def code(i):
        a[i] = i

    @always_comb
    def code_self(self, i):
        a[i] = 0

    try:
        mod.add_always(code)
        assert False
    except AssertionError:
        pass

    try:
        mod.add_always(code, j=1)
        assert False
    except AssertionError:
        pass

    try:
        mod.add_always(code_self)
        assert False
    except AssertionError:
        pass

    mod.add_always(code, i=0)
    mod.add_always(code, i=1)
    mod.add_always(code_self, i=2)
    src = verilog(mod)["mod"]
    assert "a[0] = 1'h0;" in src
    assert "a[1] = 1'h1;" in src
    assert "a[2] = 1'h0;" in src


def test_bit_loop_slicing():
    mod = Generator("mod")
    a = mod.var("a", 1)

    @always_comb
    def code():
        for i in range(1):
            a[i] = i

    mod.add_always(code)
    src = verilog(mod)["mod"]
    assert "a = 1'h0" in src

    mod = Generator("mod")
    a = mod.var("a", 4)
    clk = mod.clock("clk")

    @always_ff((posedge, clk))
    def code():
        for i in range(3):
            if a[i]:
                a[i] = 1
    mod.add_always(code)
    src = verilog(mod)["mod"]
    assert "a[2'(i)] <= 1'h1;" in src


def test_port_cast_child():
    parent = Generator("mod")
    a = parent.var("a", 1)
    b = parent.var("b", 1)
    c = kratos.util.clock(a & b)

    child = Generator("child")
    parent.add_child("child", child)
    p = child.clock("clk")
    parent.wire(c, p)

    src = verilog(parent)["mod"]
    assert ".clk(child_clk)" in src
    assert "assign child_clk = a & b;" in src


def test_always_latch(check_gold):
    from kratos import always_latch
    mod = Generator("mod")
    a = mod.input("a", 1)
    b = mod.output("b", 1)

    @always_latch
    def code():
        if a:
            b = 1

    mod.add_always(code)
    check_gold(mod, gold_name="test_always_latch", reorder_stmts=True)


def test_scope_keyword():
    mod = Generator("mod")
    scope = mod.var("a", 1)

    @always_comb
    def code():
        pass

    try:
        mod.add_always(code)
        assert False
    except SyntaxError:
        pass


@pytest.mark.skipif(not kratos.pyast.has_format_string(), reason="format string not supported in Python")
def test_loop_format_str():
    mod = Generator("mod")
    for i in range(2):
        mod.add_child(f"a_{i}", Generator("child"))
        mod[f"a_{i}"].input("a", 1)

    @always_comb
    def code():
        for i in range(2):
            mod[f"a_{i}"].ports["a"] = 1

    mod.add_always(code)
    src = verilog(mod)["mod"]
    for j in range(2):
        assert f"child a_{j}" in src


def test_attribute_lookup():
    mod = Generator("mod")

    class NewAttr(Attribute):
        def __init__(self):
            super().__init__()
            self.value = "42"

    attr = NewAttr()
    mod.add_attribute(attr)
    result = mod.find_attribute(lambda a: isinstance(a, NewAttr))
    assert len(result) == 1
    assert result[0] == attr


def test_param_set_value_instance():
    child = Generator("child")
    parent = Generator("parent")
    child.parameter("P", 32, 0)
    parent.add_child("inst", child, P=3)
    src = verilog(parent, optimize_passthrough=False)["parent"]
    assert "child #(\n  .P(32'h3))\ninst()" in src


def test_ports_vars_iter():
    mod = Generator("mod")
    mod.input("a", 1)
    mod.var("b", 1)
    mod.output("c", 1)
    mod.parameter("P1", 1)
    mod.parameter("P2", 1)
    ports = set()
    for port_name in mod.ports:
        ports.add(port_name)
    assert len(ports) == 2
    assert "a" in ports
    assert "c" in ports
    vs = set()
    for var_name, _ in mod.vars:
        vs.add(var_name)
    assert len(vs) == 3
    params = set()
    for param_name, _ in mod.params:
        params.add(param_name)
    assert len(params) == 2


def test_param_initial_codegen():
    child1 = Generator("child1")
    child1.parameter("P", 16, initial_value=5)
    parent1 = Generator("parent1")
    parent1.add_child("inst", child1, P=2)
    src = verilog(parent1, optimize_passthrough=False)["parent1"]
    assert ".P(16'h2))\ninst();" in src

    child2 = Generator("child2")
    child2.parameter("P", 16, initial_value=5)
    parent2 = Generator("parent2")
    parent2.add_child("inst", child2, P=5)
    src = verilog(parent2, optimize_passthrough=False)["parent2"]
    assert "child2 inst()" in src


def test_port_from_def():
    mod1 = Generator("mod1")
    p1 = mod1.input("p", 4)
    mod2 = Generator("mod2")
    p2 = mod2.port_from_def(p1)
    assert str(p1) == str(p2)
    assert p1.width == p2.width


def test_var_from_def():
    mod = Generator("mod")
    v1 = mod.var("v1", 2, size=[2, 3])
    v2 = mod.var_from_def(v1, "v2")
    assert v2.width == v1.width
    assert v2.name == "v2"
    p1 = mod.input("p1", 42)
    v3 = mod.var_from_def(p1, "v3")
    assert v3.width == 42


def test_raw_import():
    mod = Generator("mod")
    mod.internal_generator.add_raw_import("pkg_name")
    src = verilog(mod, optimize_passthrough=False)["mod"]
    assert "module mod \n  import pkg_name::*;\n(\n);\n\nendmodule" in src


def test_generator_port_connected():
    child = Generator("child")
    parent = Generator("parent")
    in1 = parent.var("a", 1)
    in2 = child.input("a", 1)
    out1 = parent.output("b", 1)
    out2 = child.output("b", 1)
    un_c = child.input("c", 1)
    parent.add_child("inst", child, a=in1, b=out1)
    assert in2.connected()
    assert out2.connected()
    assert not un_c.connected()


def test_port_type():
    mod = Generator("mod")
    struct = PackedStruct("config", [("read", 16), ("write", 16)])
    # make it external to test if we can skip the generation
    struct.external = True
    in1 = mod.input("in1", struct)
    enum = kratos.enum("color", ["color", "green"])
    enum.external = True
    in2 = mod.input("in_enum", enum)
    # raw types
    param = mod.param("type_t", is_raw_type=True)
    param.value = "pkg::new_type_t"
    mod.parameter("type2", is_raw_type=True, initial_value="pkg::new_type_t")
    mod.parameter("type3", is_raw_type=True, initial_value="pkg::new_type_t")
    p_width = mod.parameter("P_width", value=5)
    a_in = mod.input("a", p_width)

    # raw type port
    # width 5 should be ignored. this is just for testing
    p = mod.input("in_raw", width=5)
    p.raw_type_param = param
    assert param.param_type == kratos.ParamType.RawType
    src = verilog(mod)["mod"]
    assert "type type_t" in src
    assert "input config in1" in src
    assert "input color in_enum" in src
    assert "input type_t in_raw" in src
    assert "parameter type type_t = pkg::new_type_t" in src

    # test raw type codegen with a parent
    parent = Generator("parent")
    p_raw = parent.parameter("p_type", is_raw_type=True,
                             value="pkg::old_value_t")
    param.raw_type_param = p_raw
    param.value = p_raw

    parent.port_from_def(in1)
    parent.port_from_def(in2)
    parent.port_from_def(p)
    parent.port_from_def(a_in, check_param=False)
    parent.add_child("inst", mod, in1=parent.ports.in1,
                     in_enum=parent.ports.in_enum,
                     in_raw=parent.ports.in_raw,
                     a=parent.ports.a)

    src = verilog(parent)["parent"]
    assert "type_t(p_type)" in src
    assert ".P_width(32'h5)" in src


def test_param_size(check_gold):
    mod = Generator("mod")
    width = mod.parameter("WIDTH", 16, 8)
    addr_width = mod.parameter("ADDR_WIDTH", 16, 8)
    data_in = mod.input("data_in", width)
    addr = mod.input("addr", addr_width)
    clk = mod.clock("clk")
    mem = mod.var("data", width, size=2 ** addr_width)

    @always_ff((posedge, clk))
    def code():
        mem[addr] = data_in

    mod.add_always(code)

    check_gold(mod, "test_param_size")


def test_param_packed_struct_array(check_gold):
    mod = Generator("mod")
    struct = PackedStruct("bus", [("read", 16), ("write", 16)])
    param = mod.parameter("P", 32, 42)
    out = mod.output("out", struct, size=[param])
    var = mod.var("v", struct, size=[param])
    mod.add_stmt(out.assign(var))

    check_gold(mod, "test_param_packed_struct_array")

    assert out[0]["write"].width == 16


def test_param_copy_def():
    enum = kratos.enum("enum_t", ["A", "B"])
    enum.external = True
    child = Generator("child")
    p1 = child.parameter("P1")
    p2 = child.parameter("P2", is_raw_type=True)
    p3 = child.parameter("P3", enum)
    top = Generator("top")
    top.param_from_def(p1)
    top.param_from_def(p2, "P_t")
    top.param_from_def(p3)
    src = verilog(top)["top"]

    assert "parameter P1" in src
    assert "parameter enum_t P3" in src
    assert "parameter type P_t" in src


def test_multi_gen():
    from kratos.util import enable_multi_generate
    enable_multi_generate()

    class Mod(Generator):
        def __init__(self):
            super().__init__("mod")
            a = self.input("a", 1)
            b = self.output("b", 1)
            self.wire(a, b)
    mod1 = Mod()
    verilog(mod1)
    mod2 = Mod()
    mod2.ports.a.name = "a2"
    src = verilog(mod2)
    assert "mod" not in src
    assert "mod_unq0" in src


def test_param_resize():
    mod = Generator("mod")
    p = mod.parameter("P")
    a = mod.var("a", 5)
    b = mod.var("b", 5)
    mod.add_stmt(b.assign(a + p))


def test_clog2_var():
    from kratos import clog2
    mod = Generator("mod")
    num = mod.parameter("num", value=32)
    num2 = mod.parameter("num2", value=1)
    c = clog2(num2)
    mod.input("a", 16, size=clog2(num))
    b = mod.input("b", 16, size=clog2(num), packed=True)
    c = mod.var("c", c)

    src = verilog(mod, filename="test.sv", remove_unused=False)["mod"]
    assert "input logic [15:0] a [($clog2 (num))-1:0]" in src
    assert "input logic [($clog2 (num))-1:0] [15:0] b" in src
    assert "logic [$clog2 (num2)-1:0] c" in src
    # test slicing
    d = mod.var("d", 1)
    e = b[d]
    assert str(e) == "b[d]"
    f = c[d]
    assert str(f) == "c[d]"


def test_ssa_transform(check_gold):
    mod = Generator("mod", debug=True)
    a = mod.var("a", 4)
    b = mod.var("b", 4)
    c = mod.output("c", 4)

    @always_comb
    def func():
        a = 1
        a = 2
        if a == 2:
            a = b + a
        if a == 3:
            b = 2
        else:
            if a == 4:
                b = 3
            else:
                b = 4
                # this is not a latch
                a = 5
        c = a

    mod.add_always(func, ssa_transform=True)
    check_gold(mod, "test_ssa_transform", ssa_transform=True)
    # check if the local variable mapping is fixed
    # assign a_5 = (a_3 == 4'h4) ? a_3: a_4;
    # which corresponds to a = 5
    # notice that a should be pointing to a = b + a, since it's the last
    # time a gets assigned
    stmt = mod.get_stmt_by_index(6)
    scope = stmt.scope_context
    is_var, a_mapping = scope["a"]
    assert is_var
    # this is assign a_2 = b + a_1;
    stmt = mod.get_stmt_by_index(5)
    assert str(a_mapping) == str(stmt.left)

    # test enable table extraction
    from _kratos.passes import compute_enable_condition
    enable_map = compute_enable_condition(mod.internal_generator)
    assert len(enable_map) > 5


def test_enable_condition_always_ff():
    mod = Generator("mod")
    a = mod.var("a", 4)
    b = mod.var("b", 1)
    clk = mod.clock("clk")

    @always_ff((posedge, clk))
    def logic():
        if b:
            a = 0
        else:
            a = 1

    mod.add_always(logic)
    from _kratos.passes import compute_enable_condition
    enable_map = compute_enable_condition(mod.internal_generator)
    assert len(enable_map) == 2


def test_var_rename():
    import _kratos
    mod = Generator("mod")
    a = mod.var("a", 1)
    b = mod.input("b", 1)
    a.rename("c")
    b.rename("d")
    assert "c" in mod.vars
    assert "a" not in mod.vars
    assert "c" == a.name
    try:
        a.name = "d"
        assert False
    except _kratos.exception.UserException:
        pass


def test_merge_const_port_assignment():
    mod = Generator("mod")
    a = mod.var("a", 1)
    child = Generator("child")
    b = child.input("b", 1)
    mod.add_child("child", child, b=a)
    mod.add_stmt(a.assign(1))
    v = verilog(mod)["mod"]
    assert ".b(1'h1)" in v


def test_gen_inst_lift(check_gold):
    num_inst = 4
    parent = Generator("parent")
    clk = parent.clock("clk")
    a_array = parent.var("a", 1, size=4)
    b_array = parent.var("b", 1, size=4)
    children = []

    for i in range(num_inst):
        child = Generator("child")
        child.clock("clk")
        a = child.input("a", 1)
        b = child.output("b", 1)
        child.wire(a, b)
        parent.add_child(f"child_{i}", child,
                         clk=clk,
                         a=a_array[i],
                         b=b_array[i])
        children.append(child)

    check_gold(parent, "test_gen_inst_lift", lift_genvar_instances=True)
    name = children[1].internal_generator.handle_name()
    assert name == "parent.child.inst[1]"

    # another one that will fail the genvar test
    Generator.clear_context()
    num_inst = 4
    parent = Generator("parent")
    clk = parent.clock("clk")
    a_array = parent.var("a", 1, size=2)

    for i in range(2):
        child = Generator("child")
        child.clock("clk")
        child.input("a", 1)
        parent.add_child(f"child_{i}", child,
                         clk=clk,
                         a=a_array[0])
    src = verilog(parent, lift_genvar_instances=True)["parent"]
    assert "genvar" not in src


def test_add_child_interface_port_wiring(check_gold):
    from kratos import Interface
    mod = Generator("mod")

    class ConfigInterface(Interface):
        def __init__(self):
            Interface.__init__(self, "Config")
            self.input("read", 1, 1)
            self.output("write", 1, 1)

    interface = ConfigInterface()
    i1 = mod.interface(interface, "bus")
    # wire local variables to the interface
    read = mod.var("read", 1)
    write = mod.var("write", 1)
    mod.wire(i1.read, read)
    mod.wire(write, i1.write)

    # create child module and use the interface as port
    child = Generator("child")
    i2 = child.interface(interface, "bus2", True)
    child.wire(i2.write, i2.read)

    # wire the interface using add_child
    mod.add_child("child", child, bus2=i1)
    check_gold(mod, "test_add_child_interface_port_wiring",
               optimize_passthrough=False)


def test_auto_insert_clk_gate_skip():
    from _kratos.passes import auto_insert_clock_enable

    class Mod(Generator):
        def __init__(self, add_self, add_always):
            super(Mod, self).__init__("mod")
            clk = self.clock("clk")
            a = self.var("a", 1)
            self.clock_en("clk_en")

            @always_ff((posedge, clk))
            def code():
                a = 1

            b = self.add_always(code)
            if add_always:
                b.add_attribute("dont_touch")
            if add_self:
                self.add_attribute("dont_touch")
    m = Mod(False, False)
    auto_insert_clock_enable(m.internal_generator)
    src = verilog(m)["mod"]
    assert "if (clk_en)" in src
    m = Mod(False, True)
    auto_insert_clock_enable(m.internal_generator)
    src = verilog(m)["mod"]
    assert "if (clk_en)" not in src
    m = Mod(True, False)
    auto_insert_clock_enable(m.internal_generator)
    src = verilog(m)["mod"]
    assert "if (clk_en)" not in src


def test_final_block():
    from kratos import final

    mod = Generator("mod")
    a = mod.var("a", 1)

    @final
    def code():
        a = 1

    mod.add_always(code)
    src = verilog(mod)["mod"]
    assert "final begin\n  a = 1'h1;\nend" in src


def test_struct_of_struct(check_gold):
    mod = Generator("mod")
    struct1 = PackedStruct("struct1")
    struct1.add_attribute("value1", 32)
    struct0 = PackedStruct("struct0")
    struct0.add_attribute("value2", struct1)
    v = mod.var("v", struct0)
    v_array = mod.var("v_array", struct0, size=4)
    mod.add_stmt(v["value2"]["value1"].assign(1))
    mod.add_stmt(v_array[0]["value2"]["value1"].assign(1))
    check_gold(mod, "test_struct_of_struct")


if __name__ == "__main__":
    from conftest import check_gold_fn
    test_struct_of_struct(check_gold_fn)
