from kratos import Generator, always_ff, verilog, Attribute, posedge


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


def test_wire_merge(check_gold):
    class TestModule(Generator):
        def __init__(self, width):
            super().__init__("Test")
            self.input("in", width)
            self.output("out", width)

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


def test_simple_pipeline(check_gold):
    mod = PassThroughMod()
    # add a clock
    mod.clock("clk")
    attr = Attribute()
    attr.type_str = "pipeline"
    attr.value_str = "2"
    mod.add_attribute(attr)

    check_gold(mod, "test_simple_pipeline", insert_pipeline_stages=True)


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


def test_optimize_inline(check_gold):
    parent = Generator("parent")
    child = Generator("child")
    child.add_attribute("inline")
    parent.clock("clk")
    clk = child.clock("clk")
    a = child.input("a", 1)
    b = child.output("b", 1)

    @always_ff((posedge, clk))
    def code():
        if a:
            b = 1
        else:
            b = 0

    child.add_code(code)

    v1 = parent.var("v1", 1)
    v2 = parent.var("b", 1)
    parent.add_child("inst", child, clk=parent.ports.clk, a=v1, b=v2)

    check_gold(parent, "test_optimize_inline")


if __name__ == "__main__":
    from conftest import check_gold_fn
    test_optimize_inline(check_gold_fn)
