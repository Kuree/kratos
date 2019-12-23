from kratos import IRVisitor, Generator, PortDirection, Port, VarSlice, \
    VarVarSlice


def test_ir_port(check_gold):
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
    check_gold(mod, "test_ir_port",
               additional_passes={"name_change": change_name})


def test_ir_slice():
    def collect_slice(generator):
        class Visitor(IRVisitor):
            def __init__(self):
                IRVisitor.__init__(self)
                self.hit_slice = False
                self.hit_var_slice = False

            def visit(self, node):
                if isinstance(node, VarVarSlice):
                    assert node.sliced_by_var
                    self.hit_var_slice = True
                elif isinstance(node, VarSlice):
                    assert not node.sliced_by_var
                    self.hit_slice = True

        visitor = Visitor()
        visitor.visit_root(generator)
        return visitor

    class Mod(Generator):
        def __init__(self):
            Generator.__init__(self, "mod")
            a = self.var("a", 8)
            b = self.var("b", 3)
            d = a[2]
            c = a[b]
            self.wire(self.output("out0", 1), d)
            self.wire(self.output("out1", 1), c)

    mod = Mod()
    v = collect_slice(mod.internal_generator)
    assert v.hit_slice
    assert v.hit_var_slice


if __name__ == "__main__":
    test_ir_slice()
