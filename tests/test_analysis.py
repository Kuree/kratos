from kratos import Generator, PortDirection, PortType, always_ff, \
    verilog, StmtException, posedge


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


def test_merge_const_port_assignment():
    mod = Generator("mod")
    a = mod.var("a", 1)
    child = Generator("child")
    b = child.input("b", 1)
    mod.add_child("child", child, b=a)
    mod.add_stmt(a.assign(1))
    v = verilog(mod)["mod"]
    assert ".b(1'h1)" in v
