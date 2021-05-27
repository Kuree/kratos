from kratos import IRVisitor, Generator, PortDirection, Port, VarSlice, \
    VarVarSlice, Attribute


def test_attribute():
    mod = Generator("mod")
    a = mod.input("a", 1)
    b = mod.output("b", 1)
    mod.wire(b, a)
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


def test_ir_annotation_wiring():
    from kratos import Attribute, verilog
    import kratos
    parent = Generator("parent")
    child = Generator("child")
    parent.add_child("child_inst", child)
    port = child.input("target_port", 1)
    child.wire(child.output("out", 1), port)
    tag = "target"
    port.add_attribute(Attribute.create(tag))

    # this is a pass
    def wire_up_port(generator):
        class WireUpVisitor(IRVisitor):
            def __init__(self):
                IRVisitor.__init__(self)
                self.tag = tag

            def visit(self, node):
                if isinstance(node, kratos.Port) and node.has_attribute(self.tag):
                    # need to wire it to the instances parent and up
                    gen = node.generator
                    parent_gen = gen.parent_generator()
                    child_port = node
                    while parent_gen is not None:
                        # create a port based on the target's definition
                        p = parent_gen.port(child_port)
                        parent_gen.wire(child_port, p)
                        # move up the hierarchy
                        child_port = p
                        parent_gen = parent_gen.parent_generator()

        v = WireUpVisitor()
        v.visit_root(generator)

    wire_up_port(parent.internal_generator)

    assert "target_port" in parent.ports
    # check all the connectivity
    verilog(parent)


if __name__ == "__main__":
    test_ir_annotation_wiring()
