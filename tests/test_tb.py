from kratos import Generator, TestBench, initial, assert_, delay, Sequence, \
    BlockEdgeType
import os
import filecmp
import tempfile


def check_gold(src, gold_name):
    with tempfile.TemporaryDirectory() as tempdir:
        filename = os.path.join(tempdir, "test.sv")
        gold = os.path.join(os.path.dirname(__file__), "gold",
                            gold_name + ".sv")
        with open(filename, "w+") as f:
            f.write(src)
        assert os.path.isfile(gold)
        assert os.path.isfile(filename)
        if not filecmp.cmp(filename, gold):
            with open(filename) as f:
                print(f.read())
            print("-" * 80)
            with open(gold) as f:
                print(f.read())
            assert False


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


def test_tb_codegen():
    dut, tb = tb_dut_setup()

    @initial
    def code():
        tb.vars["in"] = 1
        assert_(tb.vars.out == 1)
        # access internal signal
        assert_(dut.vars.val == 1)

    tb.add_code(code)

    src = tb.codegen()
    check_gold(src, "test_tb_codegen")


def test_tb_delay():
    dut, tb = tb_dut_setup()

    @initial
    def code():
        delay(1, tb.vars["in"].assign(1))

    tb.add_code(code)
    src = tb.codegen()
    check_gold(src, "test_tb_delay")


def test_tb_sequence():
    dut, tb = tb_dut_setup()
    # add a clock and wire them together
    tb.wire(dut.clock("clk"), tb.var("clk", 1))

    seq = Sequence(tb.vars["in"] == 1)
    seq.imply(tb.vars.out == 1).wait(1).imply(tb.vars.out == 0)

    tb.property("test_out", seq)

    src = tb.codegen()
    check_gold(src, "test_tb_sequence")


if __name__ == "__main__":
    test_tb_sequence()
