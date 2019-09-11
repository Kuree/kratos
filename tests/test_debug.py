from kratos import Generator, DebugDataBase, verilog
import _kratos
import sqlite3
import tempfile
import os


def test_db_dump():
    mod = Generator("mod", True)
    comb = mod.combinational()
    comb.add_stmt(mod.var("a", 1).assign(mod.var("b", 1)))

    with tempfile.TemporaryDirectory() as temp:
        debug_db = os.path.join(temp, "debug.db")
        # hashing and generate verilog
        verilog(mod, debug_db_filename=debug_db)
        conn = sqlite3.connect(debug_db)
        c = conn.cursor()
        c.execute("SELECT * from breakpoint")
        result = c.fetchall()
        assert len(result) == 1

def test_debug_mock():
    # this is used for the runtime debugging
    class Mod(Generator):
        def __init__(self):
            super().__init__("mod", True)

            # ports
            self.in1 = self.input("in1", 16)
            self.in2 = self.input("in2", 16)
            self.out = self.output("out", 16)

            self.add_code(self.code)

        def code(self):
            if self.in1 == 2:
                self.out = 2
            elif self.in1 == 1:
                self.out = 0
            elif self.in2 == 1:
                self.out = 1
            else:
                self.out = 3

    with tempfile.TemporaryDirectory() as temp:
        mod = Mod()
        debug_db = os.path.join(temp, "debug.db")
        filename = os.path.join(temp, "test.sv")
        # inject verilator public
        _kratos.passes.insert_verilator_public(mod.internal_generator)
        verilog(mod, filename=filename, debug_db_filename=debug_db)


if __name__ == "__main__":
    test_debug_mock()

