from kratos import Generator, PortDirection, PortType, always, \
    verilog, is_valid_verilog, VarException, StmtException, IRVisitor, \
    PackedStruct, Port, Attribute, zext, posedge, PortBundle, const, comment,\
    enable_runtime_debug
from _kratos.passes import uniquify_generators, hash_generators_parallel
import os
import tempfile
import filecmp


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


def check_gold(mod, gold_name, **kargs):
    with tempfile.TemporaryDirectory() as tempdir:
        filename = os.path.join(tempdir, "test.sv")
        gold = os.path.join(os.path.dirname(__file__), "gold",
                            gold_name + ".sv")
        verilog(mod, filename=filename, **kargs)
        assert os.path.isfile(gold)
        assert os.path.isfile(filename)
        if not filecmp.cmp(filename, gold):
            with open(filename) as f:
                print(f.read())
            print("-" * 80)
            with open(gold) as f:
                print(f.read())
            assert False


def check_file(src_str, gold_filename):
    gold = os.path.join(os.path.dirname(__file__), "gold",
                        gold_filename)
    with open(gold) as f:
        gold_text = f.read()
        if os.path.isfile(src_str):
            with open(src_str) as ff:
                src_str = ff.read()
        if src_str != gold_text:
            print(src_str)
            print("-" * 80)
            print(gold_text)
            assert False


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
        self.add_code(self.seq_code_block)

        self.add_code(self.comb_code_block)

    @always((posedge, "clk"), (posedge, "rst"))
    def seq_code_block(self):
        if self._rst:
            self._val = 0
        else:
            self._val = self._in

    def comb_code_block(self):
        self._out = self._val


def test_async_reg():
    reg_width = 16
    reg = AsyncReg(reg_width)
    check_gold(reg, "test_async_reg")


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


def test_wire_const():
    mod = Generator("test")
    out_ = mod.output("out", 1)
    mod.wire(out_, 1)

    mod_src = verilog(mod)
    assert is_valid_verilog(mod_src)


def test_else_if():
    class ElseIf(Generator):
        def __init__(self):
            super().__init__("elseif")
            self._in0 = self.port("in0", 1, PortDirection.In)
            self._in1 = self.port("in1", 1, PortDirection.In)
            self._out = self.port("out", 1, PortDirection.Out)

            self.add_code(self.else_if)

        def else_if(self):
            if self._in0 == const(1, 1):
                self._out = 1
            elif self._in1 == const(1, 1):
                self._out = 0
            else:
                self._out = 1

    mod = ElseIf()
    check_gold(mod, "test_else_if")


def test_mod_instantiation():
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


def test_for_loop():
    class Module(Generator):
        def __init__(self, num_var: int):
            super().__init__("mod", True)
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
    check_gold(mod, "test_for_loop")


def test_switch():
    class Switch(Generator):
        def __init__(self):
            super().__init__("switch_test")

            self._in = self.port("in", 3, PortDirection.In)
            self._out = self.port("out", 3, PortDirection.Out)

            self.add_code(self.logic)

        def logic(self):
            if self._in == const(0, 3):
                self._out = 0
            elif self._in == const(1, 3):
                self._out = 1
            else:
                self._out = 2

    mod = Switch()
    check_gold(mod, "test_switch")


def test_pass_through():
    mod = PassThroughTop()
    # turn off pass through module optimization since it will remove
    # mod2 completely
    check_gold(mod, "test_pass_through", optimize_passthrough=True)


def test_nested_if():
    class Mod(Generator):
        def __init__(self):
            super().__init__("mod1")
            self.in_ = self.port("in", 2, PortDirection.In)
            self.out_ = self.port("out", 2, PortDirection.Out)

            self.add_code(self.nested_if)

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


def test_fanout_mod_inst():
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

            self.add_code(self.code)

        def code(self):
            self.out_ = self.mod_1.out_ + self.mod_2.out_

    #mod = Mod2()
    #check_gold(mod, "test_fanout_mod_inst", optimize_passthrough=False)
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
            if self.in_ == const(1, 1):
                self.out_ = const(1, 4)
            else:
                self.out_ = const(1, 1)

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

        @always((posedge, "clk"))
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


def test_static_eval_for_loop():
    class Mod(Generator):
        def __init__(self, num_loop):
            super().__init__("mod1", True)
            self.in_ = self.port("in", 1, PortDirection.In)
            self.out_ = self.port("out", num_loop, PortDirection.Out)
            self.num_loop = num_loop

            self.add_code(self.code)

        def code(self):
            if self.in_ == const(1, 1):
                for i in range(self.num_loop):
                    self.out_[i] = 1
            else:
                for i in range(self.num_loop):
                    self.out_[i] = 0

    loop = 4
    mod = Mod(loop)
    mod_src, mod_debug = verilog(mod, debug=True)
    mod_mapping = mod_debug["mod1"]
    lines = list(mod_mapping.keys())
    lines.sort()
    for ii in range(len(mod_mapping) - loop, len(mod_mapping) - 1):
        assert mod_mapping[lines[-1]][-1] == mod_mapping[lines[ii]][-1]
    Generator.clear_context()
    check_gold(mod, "test_static_eval_for_loop")


def test_pass():
    def change_name(generator):
        class Visitor(IRVisitor):
            def __init__(self):
                IRVisitor.__init__(self)

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
    check_gold(mod, "test_pass", additional_passes={"name_change": change_name})


def test_const_port():
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
    assert mod3.def_instance == mod1

    # modify mod 3
    mod3.initialize_clone()
    mod3.in_.width = 3
    mod3.out_.width = 3
    assert not mod3.is_cloned
    check_gold(mod3, "test_create")


def test_clone():
    class Mod2(Generator):
        def __init__(self):
            super().__init__("mod2")
            self.in_ = self.port("in", 2, PortDirection.In)
            self.out_ = self.port("out", 2, PortDirection.Out)

            self.child1 = PassThroughMod.clone()
            self.child2 = PassThroughMod.clone()
            self.add_child("child1", self.child1)
            self.add_child("child2", self.child2)

            self.add_code(self.code)

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


def test_packed_struct():
    struct = PackedStruct("config_data", [("read", 16, False),
                                          ("data", 16, False)])

    class Mod(Generator):
        def __init__(self, debug=False):
            super().__init__("mod", debug=debug)
            self.port_packed("in", PortDirection.In, struct)
            self.port_packed("out", PortDirection.Out, struct)
            self.wire(self.ports["out"], self.ports["in"])

    mod = Mod()
    check_gold(mod, "test_packed_struct", optimize_passthrough=False)
    Generator.clear_context()
    mod = Mod(True)
    mod.name = "packed_struct"
    with tempfile.TemporaryDirectory() as temp:
        verilog(mod, output_dir=temp, debug=True)
        mod_file = os.path.join(temp, "packed_struct.sv")
        def_file = os.path.join(temp, "packed_struct_pkg.svh")
        import json
        # json is correct
        with open(os.path.join(temp, "packed_struct.sv.debug")) as f:
            json.load(f)
        check_file(mod_file, "packed_struct_pkg.sv")
        check_file(def_file, "packed_struct_pkg.svh")


def test_more_debug1():
    mod = PassThroughTop()
    mod_src, debug_info = verilog(mod, debug=True)
    debug = debug_info["top"]
    assert is_valid_verilog(mod_src)
    assert len(debug) > 3


def test_more_debug2():
    class Top(Generator):
        def __init__(self):
            super().__init__("top", True)

            self.port("in", 1, PortDirection.In)
            self.port("out", 1, PortDirection.Out)

            pass_through = PassThroughMod()
            self.add_child("pass", pass_through)
            self.wire(self["pass"].ports["in"], self.ports["in"], )

            self.add_code(self.code_block)

        def code_block(self):
            self.ports.out = self["pass"].ports.out

    mod = Top()
    mod_src, debug_info = verilog(mod, debug=True)
    debug = debug_info["top"]
    assert is_valid_verilog(mod_src)
    assert len(debug) > 3


def test_verilog_file():
    mod = PassThroughTop()
    with tempfile.TemporaryDirectory() as tempdir:
        filename = os.path.join(tempdir, "mod.sv")
        verilog(mod, filename=filename, debug=True, optimize_passthrough=False)
        with open(filename) as f:
            src = f.read()
            assert is_valid_verilog(src)


def test_attribute():
    mod = PassThroughTop()
    stmt = mod.get_stmt_by_index(0)

    class TestAttribute(Attribute):
        def __init__(self):
            Attribute.__init__(self)
            self.value = 42
            self.value_str = "42"

    stmt.add_attribute(TestAttribute())

    assert len(mod.get_stmt_by_index(0).get_attributes()) > 0
    attr = mod.get_stmt_by_index(0).get_attributes()[0].get()
    assert attr.value == 42
    assert attr.value_str == "42"
    assert attr.type_str == "python"


def test_wire_merge():
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


def test_zero_ext():
    mod = Generator("mod", debug=True)
    out_ = mod.port("out", 2, PortDirection.Out)
    in_ = mod.port("in", 1, PortDirection.In)
    mod.wire(out_, zext(in_, 2))

    mod_src = verilog(mod)
    is_valid_verilog(mod_src)


def test_port_array():
    mod = Generator("mod", True)
    in_ = mod.port("in", 2, PortDirection.In, size=2)
    out1 = mod.port("out1", 2, PortDirection.Out, size=2)
    out2 = mod.port("out2", 2, PortDirection.Out, size=2)
    mod.wire(out1, in_)
    mod.wire(out2[0][0], in_[0][1])
    mod.wire(out2[0][1], in_[0][0])
    mod.wire(out2[1], in_[1])

    check_gold(mod, "test_port_array")


def test_simple_pipeline():
    mod = PassThroughMod()
    # add a clock
    mod.clock("clk")
    attr = Attribute()
    attr.type_str = "pipeline"
    attr.value_str = "2"
    mod.add_attribute(attr)

    check_gold(mod, "test_simple_pipeline")


def test_replace():
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


def test_local_function():
    class Mod(Generator):
        def __init__(self):
            super().__init__("test")
            in_ = self.input("in", 1)
            out_ = self.output("out", 1)
            clk = self.clock("clk")

            @always((posedge, "clk"))
            def code_block():
                if clk:
                    out_ = in_

            self.add_code(code_block)

    mod = Mod()
    check_gold(mod, "test_local_function")


def test_reg_next():
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


def test_reg_init():
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


def test_reg_enable():
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


def test_ternary():
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


def test_bundle():
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


def test_named_block():
    mod = Generator("mod", debug=True)
    out_ = mod.output("out", 1)
    in_ = mod.port("in", 1, PortDirection.In)
    comb = mod.combinational()
    if_ = comb.if_(in_ == 1)
    if_.then_(out_(0)).else_(out_(1))
    mod.mark_stmt("TEST", if_.then_body())

    def code():
        out_ = 1

    mod.add_code(code, label="TEST2")

    check_gold(mod, "test_named_block")


def test_enum():
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


def test_fsm():
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

    check_gold(mod, "test_fsm")
    # output fsm graph
    dot = fsm.dot_graph()
    check_file(dot, "test_fsm.dot")
    csv = fsm.output_table()
    check_file(csv, "test_fsm.csv")


def test_fsm_mealy():
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
    check_gold(mod, "test_fsm_mealy")


def test_function():
    from kratos.func import function

    class Mod(Generator):
        def __init__(self):
            super().__init__("mod", debug=True)
            self._in = self.input("in", 2)
            self._out = self.output("out", 2)
            self._out2 = self.output("out2", 2)

            self.add_code(self.code)

        @function
        def update_out(self, value, predicate):
            self._out2 = value
            if predicate:
                return value + self._in
            else:
                return value

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

            self.add_code(self.code)

        @function
        def update_out(self, value, predicate):
            self._out = value
            if predicate:
                return value + self._in

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


def test_reg_file():
    class Mod(Generator):
        def __init__(self):
            super().__init__("mod")
            self._in = self.input("in", 4)
            self._out = self.output("out", 4)
            self.waddr = self.input("warr", 2)
            self.raddr = self.input("raddr", 2)
            self.reg = self.var("reg_file", 4, size=4)

            self.add_code(self.code)

        def code(self):
            self.reg[self.waddr] = self._in
            self._out = self.reg[self.raddr]

    mod = Mod()
    check_gold(mod, "test_reg_file")


def test_comment():
    class Mod(Generator):
        def __init__(self):
            super().__init__("mod")
            self._in = self.input("in", 1)
            self._out = self.output("out", 1)
            self._out2 = self.output("out2", 1)
            self.var = self.var("v", 1)

            child = PassThroughMod()
            self.add_child("child", child, "This is a comment")
            self.wire(self._in, child.in_)
            self.wire(self._out, child.out_)
            self.wire(self._out2, self.var)

            comment(self._in, "Input port")
            comment(self.var, "variable comment")
    mod = Mod()
    check_gold(mod, "test_comment", optimize_passthrough=False)


def test_packed_array():
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


def test_c_dpi_function():
    from kratos.func import dpi_function

    @dpi_function(8)
    def add(arg0, arg1):
        pass

    class Mod(Generator):
        def __init__(self):
            super().__init__("mod", debug=True)
            self._in = self.input("in", 2)
            self._out = self.output("out", 8)

            self.add_code(self.code)

        def code(self):
            # because the types are inferred
            # implicit const conversion doesn't work here
            self._out = add(self._in, const(1, 2))

    mod = Mod()
    # once it's turned off, user has to handle sv logic themselves in the
    # c interface
    check_gold(mod, "test_dpi", int_dpi_interface=False)


def test_nested_fsm():
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
    check_gold(mod, "test_nested_fsm")


def test_symbol_table():
    from kratos.debug import extract_symbol_table
    mod = AsyncReg(16, True)
    verilog(mod)
    table, _ = extract_symbol_table(mod)
    assert len(table) == 1
    assert len(table[mod]) == 5


def test_breakpoint():
    from _kratos.passes import extract_debug_break_points
    mod = Generator("mod", True)
    comb = mod.combinational()
    stmt0 = mod.output("out", 1).assign(mod.input("in", 1))
    comb.add_stmt(stmt0)
    stmt1 = mod.var("val", 1).assign(mod.ports["in"])
    comb.add_stmt(stmt1)

    enable_runtime_debug(mod)
    table = extract_debug_break_points(mod.internal_generator)
    assert len(table) == 2
    assert table[stmt0] == 0
    assert table[stmt1] == 1
    check_gold(mod, "test_breakpoint")


def test_cast():
    from kratos.util import clock

    class Mod1(Generator):
        def __init__(self):
            super().__init__("mod")
            self.v = self.var("v", 1)
            self.out = self.output("out", 1)
            self.add_code(self.code)

        @always((posedge, "v"))
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
            # only procedural allowed
            seq = self.sequential((posedge, clock(self.v)))
            seq.add_stmt(self.output("out", 1).assign(const(1, 1)))

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

            @always((posedge, "clk"), (posedge, "rst"))
            def code():
                if rst:
                    out_ = 0
                elif cen:
                    out_ = in_

            self.add_code(code)

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

            @always((posedge, "clk"), (posedge, "rst"))
            def code():
                if rst:
                    out_ = 0

            self.add_code(code)

    mod = Mod()
    try:
        verilog(mod)
        assert False
    except StmtException:
        assert True


def test_param():
    mod = Generator("mod", True)
    param = mod.parameter("P", 4, 4)
    param2 = mod.parameter("P2", 4, 4)
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


if __name__ == "__main__":
    test_param()
