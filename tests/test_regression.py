from kratos import Generator, verilog
import tempfile
import os
import filecmp


class PassThroughMod(Generator):
    def __init__(self, is_clone: bool = False):
        super().__init__("mod1", True, is_clone)
        self.in_ = self.input("in", 1)
        self.out_ = self.output("out", 1)
        self.wire(self.out_, self.in_)


def check_gold(mod, gold_name, **kargs):
    with tempfile.TemporaryDirectory() as tempdir:
        filename = os.path.join(tempdir, "test.sv")
        gold = os.path.join(os.path.dirname(__file__), "gold",
                            gold_name + ".sv")
        verilog(mod, filename=filename, **kargs)
        assert os.path.isfile(gold)
        assert os.path.isfile(filename)
        if not filecmp.cmp(filename, gold):
            with open(filename) as f:
                print(f.read())
            print("-" * 80)
            with open(gold) as f:
                print(f.read())
            assert False


def test_regression_1():
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

