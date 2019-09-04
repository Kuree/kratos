from kratos import Generator, TestBench, initial, assert_
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


def test_tb_codegen():
    dut = Generator("mod")
    dut.wire(dut.output("out", 1), dut.input("in", 1))
    dut.wire(dut.var("val", 1), dut.ports["in"])

    tb = TestBench()

    tb.add_child("dut", dut)
    in_ = tb.var("in", 1)
    out_ = tb.var("out", 1)
    tb.wire(dut.ports["in"], in_)
    tb.wire(out_, dut.ports["out"])

    @initial
    def code():
        in_ = 1
        assert_(out_ == 1)
        # access internal signal
        assert_(dut.vars.val == 1)

    tb.add_code(code)

    src = tb.codegen()
    check_gold(src, "test_tb_codegen")


if __name__ == "__main__":
    test_tb_codegen()
