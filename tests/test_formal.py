from kratos import Generator, always_ff, posedge, negedge, reduce_add, verilog
from kratos.formal import output_btor
import tempfile
import os
import pytest
import shutil

has_yosys = shutil.which("yosys") is not None


class Parent(Generator):
    def __init__(self):
        super().__init__("Parent")
        in_ = self.input("in", 16)
        out = self.output("out", 16)
        clk = self.clock("clk")
        rst = self.reset("rst")

        class Child(Generator):
            def __init__(self):
                super().__init__("Child")
                child_in = self.input("child_in", 16)
                child_out = self.output("out", 16)
                child_clk = self.clock("clk")
                child_rst = self.reset("rst")

                @always_ff((posedge, child_clk), (negedge, child_rst))
                def code():
                    if ~child_rst:
                        child_out = 0
                    else:
                        child_out = child_in
                self.add_always(code)
        children = []
        for i in range(2):
            child = Child()
            children.append(child)
            self.add_child("child_{0}".format(i), child,
                           child_in=in_, clk=clk, rst=rst)
        self.wire(out, reduce_add(*[mod.ports.out for mod in children]))


@pytest.mark.skipif(not has_yosys, reason="yosys is not available")
def test_output_btor():
    p = Parent()
    with tempfile.TemporaryDirectory() as temp:
        btor_filename = os.path.join(temp, "test.btor")
        output_btor(p, btor_filename, quite=True)
        with open(btor_filename) as f:
            lines = f.readlines()
        assert len(lines) > 10


if __name__ == "__main__":
    test_output_btor()
