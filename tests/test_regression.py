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


if __name__ == "__main__":
    test_regression_packed_struct_array()
