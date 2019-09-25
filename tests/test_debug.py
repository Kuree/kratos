from kratos import Generator, always, verilog, posedge
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


def test_seq_debug():
    class Mod(Generator):
        def __init__(self):
            super().__init__("mod", True)
            # ports
            self.in_ = self.input("in1", 1)
            self.clock("clk")
            for i in range(4):
                self.output("out{0}".format(i), 1)

            self.add_code(self.code1)
            self.add_code(self.code2)

        def code1(self):
            if self.in_ == 0:
                self.ports.out0 = 0
                self.ports.out1 = 0
            else:
                self.ports.out0 = 1
                self.ports.out1 = 1

        @always((posedge, "clk"))
        def code2(self):
            if self.in_ == 0:
                self.ports.out2 = 0
                self.ports.out3 = 0
            else:
                self.ports.out2 = 1
                self.ports.out3 = 1

    mod = Mod()
    with tempfile.TemporaryDirectory() as temp:
        debug_db = os.path.join(temp, "debug.db")
        filename = os.path.join(temp, "test.sv")
        verilog(mod, filename=filename, debug_db_filename=debug_db)
        conn = sqlite3.connect(debug_db)
        c = conn.cursor()
        c.execute("SELECT * FROM breakpoint WHERE id=7")
        result = c.fetchall()
        assert len(result) == 2


def test_metadata():
    def insert_io(m):
        m.input("in", 1)
        m.output("out", 1)
        m.wire(m.ports.out, m.ports["in"])

    mod1 = Generator("mod1", True)
    insert_io(mod1)
    mod2 = Generator("mod2", True)
    insert_io(mod2)
    mod1.add_child("child", mod2)
    mod1.wire(mod2.ports["in"], mod1.ports["in"])
    mod1.wire(mod1.output("out2", 1), mod2.ports.out)
    with tempfile.TemporaryDirectory() as temp:
        debug_db = os.path.join(temp, "debug.db")
        filename = os.path.join(temp, "test.sv")
        verilog(mod1, filename=filename, debug_db_filename=debug_db,
                optimize_passthrough=False)
        conn = sqlite3.connect(debug_db)
        c = conn.cursor()
        c.execute("SELECT * FROM connection")
        conns = c.fetchall()
        assert len(conns) == 2
        assert conns[0][-1] == conns[0][1] and conns[0][1] == "in"
        assert conns[1][-1] == "out2"


def test_context():
    class Mod(Generator):
        def __init__(self, width):
            super().__init__("mod", True)
            in_ = self.input("in", width)
            out = self.output("out", width)
            sel = self.input("sel", width)
            # test self variables
            self.out = out
            self.width = width

            def code():
                if sel:
                    out = 0
                else:
                    for i in range(width):
                        out[i] = 1
            self.add_code(code)

    mod = Mod(4)
    with tempfile.TemporaryDirectory() as temp:
        debug_db = os.path.join(temp, "debug.db")
        filename = os.path.join(temp, "test.sv")
        verilog(mod, filename=filename, debug_db_filename=debug_db)
        conn = sqlite3.connect(debug_db)
        c = conn.cursor()
        c.execute("SELECT * FROM context")
        variables = c.fetchall()
        assert len(variables) > 20


if __name__ == "__main__":
    test_context()
