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
        assert len(result) == 1


def test_metadata():
    mod = Generator("mod", True)
    mod.input("in", 1)
    mod.output("out", 1)
    mod.wire(mod.ports.out, mod.ports["in"])
    with tempfile.TemporaryDirectory() as temp:
        debug_db = os.path.join(temp, "debug.db")
        filename = os.path.join(temp, "test.sv")
        verilog(mod, filename=filename, debug_db_filename=debug_db)
        conn = sqlite3.connect(debug_db)
        c = conn.cursor()
        c.execute("SELECT value FROM metadata WHERE name = ?", ["top_name"])
        value = c.fetchone()[0]
        assert value == "mod"


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


def test_hierarchy_conn():
    from functools import reduce
    mods = []
    num_child = 4
    for i in range(num_child):
        mod = Generator("mod", True)
        in_ = mod.input("in", 1)
        out_ = mod.output("out", 1)
        mod.wire(out_, in_ & 1)
        mods.append(mod)

    parent = Generator("parent", True)
    in_ = parent.input("in", 1)
    out_ = parent.output("out", 1)
    for i, mod in enumerate(mods):
        parent.add_child("mod{0}".format(i), mod)
        if i == 0:
            continue
        parent.wire(mod.ports["in"], mods[i - 1].ports.out)
    parent.wire(mods[0].ports["in"], in_)
    comb = parent.combinational()
    comb.add_stmt(out_.assign(reduce(lambda a, b: a ^ b,
                              [mod.ports.out for mod in mods])))
    with tempfile.TemporaryDirectory() as temp:
        debug_db = os.path.join(temp, "debug.db")
        filename = os.path.join(temp, "test.sv")
        verilog(parent, filename=filename, debug_db_filename=debug_db)
        conn = sqlite3.connect(debug_db)
        c = conn.cursor()
        c.execute("SELECT * FROM hierarchy")
        mods = c.fetchall()
        assert len(mods) == num_child
        c.execute("SELECT * FROM connection")
        conns = c.fetchall()
        # plus 2 because in and out from parent to mod0 and mod3
        assert len(conns) == num_child - 1 + 2


def test_clock_interaction():
    mods = []
    num_child = 4
    for i in range(num_child):
        mod = Generator("mod", True)
        in_ = mod.input("in", 4)
        out_ = mod.output("out", 4)
        clk = mod.clock("clk")
        seq = mod.sequential((posedge, clk))
        seq.add_stmt(out_.assign(in_))
        mods.append(mod)
    parent = Generator("parent", True)
    clk = parent.clock("clk")
    in_ = parent.input("in", 4)
    out = parent.output("out", 4)
    for i, mod in enumerate(mods):
        parent.add_child("mod{0}".format(i), mod)
        parent.wire(mod.ports.clk, clk)
        if i == 0:
            continue
        parent.wire(mod.ports["in"], mods[i - 1].ports.out)
    parent.wire(mods[0].ports["in"], in_)
    parent.wire(out, mods[-1].ports.out)
    with tempfile.TemporaryDirectory() as temp:
        debug_db = os.path.join(temp, "debug.db")
        filename = os.path.join(temp, "test.sv")
        verilog(parent, filename=filename, debug_db_filename=debug_db)


def test_design_hierarchy():
    from functools import reduce
    mods = []
    num_child = 4
    num_child_child = 3

    def add_child(m):
        output = None
        outputs_ = []
        for c in range(num_child_child):
            child = Generator("child", True)
            m.add_child("child{0}".format(c), child)
            in__ = child.input("in", 4)
            out__ = child.output("out", 4)
            clk__ = child.clock("clk")
            m.wire(m.ports.clk, clk__)
            if output is None:
                m.wire(m.ports["in"], in__)
            else:
                m.wire(output, in__)
            output = out__
            seq_ = child.sequential((posedge, clk__))
            seq_.add_stmt(out__.assign(in__))
            outputs_.append(out__)
        return outputs_

    for i in range(num_child):
        mod = Generator("mod", True)
        mod.input("in", 4)
        out_ = mod.output("out", 4)
        clk = mod.clock("clk")
        seq = mod.sequential((posedge, clk))
        outputs = add_child(mod)
        seq.add_stmt(out_.assign(reduce(lambda x, y: x + y, outputs)))
        mods.append(mod)
    parent = Generator("parent")
    clk = parent.clock("clk")
    in_ = parent.input("in", 4)
    out = parent.output("out", 4)
    for i, mod in enumerate(mods):
        parent.add_child("mod{0}".format(i), mod)
        parent.wire(mod.ports.clk, clk)
        if i == 0:
            continue
        parent.wire(mod.ports["in"], mods[i - 1].ports.out)
    parent.wire(mods[0].ports["in"], in_)
    parent.wire(out, mods[-1].ports.out)
    with tempfile.TemporaryDirectory() as temp:
        debug_db = os.path.join(temp, "debug.db")
        filename = os.path.join(temp, "test.sv")
        verilog(parent, filename=filename, debug_db_filename=debug_db)
        conn = sqlite3.connect(debug_db)
        c = conn.cursor()
        c.execute("SELECT * FROM hierarchy")
        mods = c.fetchall()
        assert len(mods) == num_child_child * num_child + num_child


def test_assert():
    from kratos import assert_
    mod = Generator("mod", True)
    in_ = mod.input("in", 1)
    out_ = mod.output("out", 1)

    def code():
        # we introduce this bug on purpose
        out_ = in_ - 1
        assert_(out_ == in_)

    mod.add_code(code)
    with tempfile.TemporaryDirectory() as temp:
        debug_db = os.path.join(temp, "debug.db")
        filename = os.path.join(temp, "test.sv")
        verilog(mod, filename=filename, debug_db_filename=debug_db)
        with open(filename) as f:
            content = f.read()
            assert "assert (out == in) else" in content
        conn = sqlite3.connect(debug_db)
        c = conn.cursor()
        c.execute("SELECT * FROM breakpoint")
        lines = c.fetchall()
        assert len(lines) == 2
        # they are only one line apart
        assert lines[0][2] == lines[1][2] + 1


if __name__ == "__main__":
    test_assert()
