from kratos import Generator, TestBench, initial, assert_, delay, Sequence


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

    src = tb.codegen()
    check_gold(src, "test_tb_codegen")


def test_tb_delay(check_gold):
    dut, tb = tb_dut_setup()

    @initial
    def code():
        delay(1, tb.vars["in"].assign(1))

    tb.add_always(code)
    src = tb.codegen()
    check_gold(src, "test_tb_delay")


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

    src = tb.codegen()
    check_gold(src, "test_tb_sequence")


if __name__ == "__main__":
    from conftest import check_gold_fn
    test_tb_sequence(check_gold_fn)
