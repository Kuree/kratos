import kratos
from kratos import Generator, verilog, const, always_comb, Interface
import platform
import pytest
import os


class PassThroughMod(Generator):
    def __init__(self, is_clone: bool = False):
        super().__init__("mod1", True, is_clone)
        self.in_ = self.input("in", 1)
        self.out_ = self.output("out", 1)
        self.wire(self.out_, self.in_)


def test_regression_1(check_gold):
    class Mod(Generator):
        def __init__(self):
            super().__init__("Top")
            self.in_ = self.input("i_data_in", 2)
            self.out_ = self.output("o_data_out", 2)

            child1 = PassThroughMod()
            self.add_child("child1", child1)
            self.wire(child1.in_, self.in_[0])
            self.wire(self.out_[0], child1.out_)

            child2 = PassThroughMod()
            self.add_child("child2", child2)
            self.wire(self.in_[1], child2.in_)
            self.wire(self.out_[1], child2.out_)

    mod = Mod()
    check_gold(mod, "test_regression_1", optimize_passthrough=False)


def test_regression_2():
    from kratos.func import dpi_function

    @dpi_function(8)
    def func(arg0):
        pass

    class Mod(Generator):
        def __init__(self):
            super().__init__("mod", debug=True)
            self._in = self.input("in", 2)
            self._out = self.output("out", 8)
            self._reg = self.var("val", 8)

            self.add_always(self.code)

        @always_comb
        def code(self):
            # because the types are inferred
            # implicit const conversion doesn't work here
            self._reg = func(const(1, 2))
            self._out = func(const(1, 2))

    mod = Mod()
    mod_src = verilog(mod)
    assert "func" in mod_src[1]


def test_regression_concat():
    from kratos import concat
    parent = Generator("parent")
    for i in range(2):
        child = Generator("child")
        in_ = child.input("in", 1)
        out_ = child.output("out", 1)
        child.wire(out_, in_)
        parent.add_child("child{0}".format(i), child)
    in_ = parent.input("in", 1)
    out_2 = parent.output("out2", 2)
    for i in range(2):
        parent.wire(in_, parent["child{0}".format(i)].ports["in"])
    parent.wire(out_2,
                concat(parent["child0"].ports.out, parent["child1"].ports.out))
    src = verilog(parent, optimize_passthrough=False)["parent"]
    assert "assign out2 = {child0_out, child1_out};" in src


def test_regression_flatten_array_param():
    from _kratos import create_wrapper_flatten
    mod = Generator("mod")
    p = mod.parameter("param", value=16)
    mod.input("in", width=p)
    inst = create_wrapper_flatten(mod.internal_generator, "wrapper")
    gen = Generator("", internal_generator=inst)
    src = verilog(gen)["wrapper"]
    assert "parameter param = 32'h10" in src


def test_regression_interface():
    class ConfigInterface(Interface):
        def __init__(self):
            Interface.__init__(self, "cfg_ifc")
            # Local variables
            wr_en = self.var("wr_en", 1)
            self.master = self.modport("master")
            self.slave = self.modport("slave")
            self.master.set_input(wr_en)
            self.slave.set_input(wr_en)

    class Top(Generator):
        def __init__(self):
            super().__init__("top")
            config = ConfigInterface()
            self.clk = self.clock("clk")
            self.ifc = self.interface(config.slave, "ifc_config_slave", is_port=True)

    verilog(Top())


def test_regression_packed_struct_array():
    from kratos import PackedStruct
    struct = PackedStruct("config_data", [("read", 16, False),
                                          ("data", 16, False)])

    class Parent(Generator):
        def __init__(self):
            super().__init__("parent")
            in_ = self.input("in", 16)
            out = self.output("out", struct, size=2)

            self.wire(out[0]['read'], in_)
            self.wire(out[0]['data'], in_)
            self.wire(out[1]['read'], in_)
            self.wire(out[1]['data'], in_)

    verilog(Parent(), filename="test.sv")


def test_regression_modport_interface():
    from kratos import Interface, verilog, Generator

    class ConfigInterface(Interface):
        def __init__(self):
            super(ConfigInterface, self).__init__("config_i")

            a = self.var("a", 1)
            b = self.var("b", 1)

            m = self.modport("master")
            m.set_output(a)
            self.slave = self.modport("slave")
            self.slave.set_output(b)

    interface = ConfigInterface()
    child = Generator("child")
    child_i = child.interface(interface.slave, "p", is_port=True)
    child.add_stmt(child_i.b.assign(1))
    parent = Generator("parent")
    parent_i = parent.interface(interface.slave, "p", is_port=True)
    parent.add_child("inst", child, p=parent_i)

    v = verilog(parent)["parent"]
    assert ".p(p)" in v


def test_regression_wire_merging():
    class Mod(Generator):
        def __init__(self):
            super().__init__("mod")
            self.out_ = self.output("out_", 4)

            self.arr = self.var("arr", 1, size=4)
            self.add_always(self.init)
            self.add_always(self.ctrl)

        @always_comb
        def init(self):
            for i in range(4):
                self.arr[i] = 1

        @always_comb
        def ctrl(self):
            for i in range(4):
                self.out_[i] = self.arr[i]

    m = Mod()
    v = verilog(m)["mod"]
    assert "out_[3] = arr[3];" in v


def test_regression_external_module_wiring():
    module_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "vectors", "module2.sv")

    class Parent(Generator):
        def __init__(self):
            super().__init__(f"parent")
            self.a = self.input("a", 1)
            self.f = self.output("f", 1)
            child = self.from_verilog('child', module_path, [], {})
            self.add_child("child", child)
            self.wire(child.ports['a'], self.a)
            self.wire(child.ports['f'], self.f)

    mod = Parent()
    verilog(mod)


def test_regression_struct_struct_access():
    from kratos import PackedStruct

    class StructTest(Generator):
        def __init__(self):
            super().__init__("struct_test")
            self.wr_tr_struct = PackedStruct("wr_tr_struct", [("wr_en", 1), ("wr_addr", 16)])
            self.rd_tr_struct = PackedStruct("rd_tr_struct", [("rd_en", 1), ("rd_addr", 16)])
            self.tr_struct = PackedStruct("tr_struct")
            self.tr_struct.add_attribute("wr_tr", self.wr_tr_struct)
            self.tr_struct.add_attribute("rd_tr", self.rd_tr_struct)

            self.in_ = self.input("in_", self.tr_struct)
            self.out_ = self.output("out_", 1)

            self.add_always(self.comb)

        @always_comb
        def comb(self):
            if self.in_["wr_tr"]["wr_addr"][4, 0] == 0:
                self.out_ = 1
            else:
                self.out_ = 0

    mod = StructTest()
    verilog(mod)


def test_regression_decouple_wire():
    # test reported from Jake Ke
    from kratos import ternary

    class Child(Generator):
        def __init__(self):
            super().__init__("child")
            self._a = self.input("a", 1)
            self._b = self.output("b", 1)
            self.wire(self._b, 1)

    class Parent(Generator):
        def __init__(self):
            super().__init__("parent")
            self._a_in = self.input("a_in", 1)

            child_inst = Child()
            self.add_child("child_inst", child_inst, a=self._a_in)

            self._c = self.var("c", 1)
            self.add_code(self.some_comb)

            self._d = self.var("d", 1)
            # self.wire(self._d, self._c + self["child_inst"].ports.b) # this is OK for some reason
            # I would like to get the generated wire, child_inst_b
            self.wire(self._d, ternary(self["child_inst"].ports.b, self._c, self._c))
            self._e = self.var("e", 1)
            self.add_always(self.if_comb)
            self._f = self.var("f", 1)
            self.wire(self._f, self["child_inst"].ports.a == 0)

        @always_comb
        def some_comb(self):
            self._c = self["child_inst"].ports.a # I would like to get a_in

        @always_comb
        def if_comb(self):
            if self["child_inst"].ports.a:
                self._e = 1
            else:
                self._e = 0

    mod = Parent()
    src = verilog(mod, fix_port_legality=True)["parent"]
    assert "assign d = child_inst_b ? c: c;" in src
    assert "c = a_in;" in src
    assert "if (a_in) begin" in src
    assert "assign f = a_in == 1'h0;" in src


def test_one_state_fsm():
    # example provided by Max
    class OneStateFSM(Generator):
        def __init__(self, debug: bool = False, is_clone: bool = False, internal_generator=None):
            super().__init__("onestate", debug, is_clone, internal_generator)

            self._clk = self.clock("clk")
            self._rst_n = self.reset("rst_n")

            self.boring_fsm = self.add_fsm("boring_fsm", reset_high=False)
            START = self.boring_fsm.add_state("START")

            self._boring_var = self.var("boring_var", 1)
            START.next(START, None)
            self.boring_fsm.output(self._boring_var)
            START.output(self._boring_var, 1)

            self.boring_fsm.set_start_state(START)

    mod = OneStateFSM()
    verilog(mod)


def test_and():
    mod = Generator("gen", debug=True)
    a = mod.var("a", 4)
    b = mod.var("b", 10)
    c = mod.var("c", 1)

    @always_comb
    def code():
        c = 1
        for i in range(4):
            if (i < a) and (b == const(1, 10)):
                c = 0

    mod.add_code(code)

    src = verilog(mod)["gen"]
    # notice the flipping
    assert "(a > 4'h1) && (b == 10'h1)" in src


def test_static_if():
    mod = Generator("gen")
    a = mod.output("a", 1)
    b = 1

    @always_comb
    def code():
        if b == 1:
            a = 1
        else:
            a = 0

    mod.add_always(code)
    src = verilog(mod)["gen"]
    assert "a = 1'h1" in src


def test_flush_skip(check_gold):
    # bug report from Jake Ke
    from kratos import posedge, negedge, always_ff

    class BugExample(Generator):
        def __init__(self):
            super().__init__("parent", debug=True)
            self._clk = self.clock("clk")
            self._rst_n = self.reset("rst_n")

            self._flush = self.input("flush", 1)
            self.add_attribute("sync-reset=flush")

            clk_en_port = self.clock_en("clk_en")

            self._a = self.var("a", 1)
            self._b = self.var("b", 1)
            self.add_code(self.regb)
            self.add_code(self.rega)

            kratos.passes.auto_insert_clock_enable(self.internal_generator)
            kratos.passes.auto_insert_sync_reset(self.internal_generator)

        @always_ff((posedge, "clk"), (negedge, "rst_n"))
        def rega(self):
            if ~self._rst_n:
                self._a = 0
            elif self._flush:
                self._a = 1
            else:
                self._a = ~self._a

        @always_ff((posedge, "clk"), (negedge, "rst_n"))
        def regb(self):
            if ~self._rst_n:
                self._b = 0
            else:
                self._b = ~self._b

    check_gold(BugExample(), "test_flush_skip")


@pytest.mark.skip(reason="Known to break the logic; need to fix it later")
def test_decouple_parent():
    child = Generator("child")
    child_out1 = child.output("o1", 1)
    child_out2 = child.output("o2", 2)
    child_in = child.input("in", 2)
    child.wire(child_in[0], child_out1)
    child.wire(child_in, child_out2)
    parent = Generator("parent")
    parent.add_child("c", child)
    a = parent.var("a", 1)

    parent.add_stmt(child_in.assign(0))
    parent.wire(a, (child_out1.extend(2) & child_out2[0].extend(2))[0])

    src = verilog(parent)["parent"]


def test_var_reduce_parent():
    child = Generator("child")
    a = child.input("a", 2)
    b = child.output("b", 2)
    child.wire(b, a)
    parent = Generator("parent")
    c = parent.input("c", 2)
    d = parent.var("d", 1)
    parent.add_child("inst", child, a=c)
    parent.wire(d, child.ports.b.r_or())
    parent2 = Generator("parent2")
    e = parent2.var("e", 2)
    parent2.add_child("inst", parent, c=e)

    src = verilog(parent2, optimize_passthrough=False)["parent"]
    assert "assign d = |inst_b;" in src


def test_ast_if_opt():
    mod = Generator("mod")
    c = True
    a = mod.var("a", 2)

    @always_comb
    def logic(i):
        if c:
            if i == 0:
                a[i] = 0
        else:
            a[i] = 1

    for i in range(2):
        mod.add_always(logic, i=i)


def test_ast_if_opt2():
    mod = Generator("mod")
    area_opt = True

    a = mod.input("a", 1)
    b = mod.output("b", 1)

    @always_comb
    def tb_ctrl(i):
        if a:
            if area_opt:
                if i == 0:
                    b[i] = 0
                else:
                    b[i] = 1
            else:
                b[i] = 1

    mod.add_code(tb_ctrl, i=0)


if __name__ == "__main__":
    from conftest import check_gold_fn
    test_flush_skip(check_gold_fn)
