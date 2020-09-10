from kratos import Generator, verilog, const, always_comb
import tempfile
import os
import filecmp


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


if __name__ == "__main__":
    test_regression_flatten_array_param()
