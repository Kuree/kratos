from kratos import Generator, TestBench, initial, assert_, delay, Sequence, verilog, always, posedge


def tb_dut_setup():
    dut = Generator("mod")
    dut.wire(dut.output("out", 1), dut.input("in", 1))
    dut.wire(dut.var("val", 1), dut.ports["in"])

    tb = TestBench()

    tb.add_child("dut", dut)
    in_ = tb.var("in", 1)
    out_ = tb.var("out", 1)
    tb.wire(dut.ports["in"], in_)
    tb.wire(out_, dut.ports["out"])
    return dut, tb


def test_tb_codegen(check_gold):
    dut, tb = tb_dut_setup()

    @initial
    def code():
        tb.vars["in"] = 1
        assert_(tb.vars.out == 1)
        # access internal signal
        assert_(dut.vars.val == 1)

    tb.add_always(code)

    check_gold(tb, "test_tb_codegen")


def test_tb_delay(check_gold):
    dut, tb = tb_dut_setup()

    @initial
    def code():
        delay(1, tb.vars["in"].assign(1))

    tb.add_always(code)
    check_gold(tb, "test_tb_delay")


def test_tb_sequence(check_gold):
    from kratos.util import clock
    from kratos import PropertyAction

    dut, tb = tb_dut_setup()
    # add a clock and wire them together
    tb.wire(dut.clock("clk"), clock(tb.var("clk", 1)))

    seq = Sequence(tb.vars["in"] == 1)
    seq.imply(tb.vars.out == 1).wait(1).imply(tb.vars.out == 0)

    p = tb.property("test_out", seq)
    p.action = PropertyAction.Assert

    check_gold(tb, "test_tb_sequence")


def test_display_stmt():
    from kratos.util import display
    mod = Generator("gen")
    a = mod.var("a", 1)

    @initial
    def code():
        display("%d", a)

    mod.add_always(code)

    src = verilog(mod)["gen"]
    assert '$display ("%d", a);\n' in src

    import _kratos
    from kratos.passes import check_non_synthesizable_content
    try:
        check_non_synthesizable_content(mod.internal_generator)
        assert False
    except _kratos.exception.UserException:
        pass


def test_event_control_stmt():
    mod = Generator("gen")
    a = mod.var("a", 1)

    @initial
    def code():
        posedge(a)
        delay(1, None)
        a = 1

    mod.add_always(code)

    src = verilog(mod)["gen"]
    assert "#1;\n" in src
    assert "\n  @(posedge a);\n" in src


def test_always():
    mod = Generator("mod")
    clk = mod.var("clk", 1)

    @always
    def code():
        delay(5, clk.assign(~clk))

    mod.add_always(code)

    src = verilog(mod)["mod"]
    assert "always begin\n" in src
    assert "#5 clk = ~clk;\n" in src


def test_file_ops(check_gold):
    from kratos.util import fopen, fscanf, fclose
    mod = Generator("mod")
    a = mod.var("a", 1)
    b = mod.var("b", 1)
    c = mod.var("c", 32)
    fd = mod.var("fd", 32)

    @initial
    def code():
        fd = fopen("test.sv", "r")
        for i in range(10):
            c = fscanf(fd, "%d %d", a, b)
        fclose(fd)

    mod.add_always(code)
    check_gold(mod, "test_file_ops")


def test_finish():
    from kratos.util import finish
    mod = Generator("mod")

    @initial
    def code():
        finish(0)
        finish()

    mod.add_code(code)
    src = verilog(mod)["mod"]
    assert "$finish (32'h0);\n" in src
    assert "$finish ();\n" in src


def test_task(check_gold):
    from kratos.func import task
    from kratos.util import finish

    class TB(Generator):
        def __init__(self):
            super(TB, self).__init__("TB")
            self.a = self.var("a", 1)
            self.b = self.var("b", 1)

            self.add_code(self.code)

        @task
        def delay_finish(self):
            delay(5, None)
            finish()

        @initial
        def code(self):
            self.delay_finish()

    tb = TB()
    check_gold(tb, "test_task")


if __name__ == "__main__":
    from conftest import check_gold_fn
    test_task(check_gold_fn)
