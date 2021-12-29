from kratos import Generator, always_ff, verilog, posedge, always_comb
from kratos.util import reduce_add
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
        verilog(mod, insert_debug_info=True, debug_db_filename=debug_db)
        conn = sqlite3.connect(debug_db)
        c = conn.cursor()
        c.execute("SELECT * from breakpoint")
        result = c.fetchall()
        assert len(result) == 1
        conn.close()


def test_debug_mock():
    # this is used for the runtime debugging
    class Mod(Generator):
        def __init__(self):
            super().__init__("mod", True)

            # ports
            self.in1 = self.input("in1", 16)
            self.in2 = self.input("in2", 16)
            self.out = self.output("out", 16)

            self.add_always(self.code)

        @always_comb
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
        verilog(mod, filename=filename, insert_debug_info=True,
                insert_verilator_info=True, debug_db_filename=debug_db)
        # make sure the verilator public is there
        with open(filename) as f:
            content = f.read()
        assert "verilator public" in content


def test_seq_debug():
    class Mod(Generator):
        def __init__(self):
            super().__init__("mod", True)
            # ports
            self.in_ = self.input("in1", 1)
            self.clock("clk")
            for i in range(4):
                self.output("out{0}".format(i), 1)

            self.add_always(self.code1)
            self.add_always(self.code2)

        @always_comb
        def code1(self):
            if self.in_ == 0:
                self.ports.out0 = 0
                self.ports.out1 = 0
            else:
                self.ports.out0 = 1
                self.ports.out1 = 1

        @always_ff((posedge, "clk"))
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
        verilog(mod, filename=filename, insert_debug_info=True,
                debug_db_filename=debug_db)
        conn = sqlite3.connect(debug_db)
        c = conn.cursor()
        c.execute("SELECT * FROM breakpoint WHERE id=7")
        result = c.fetchall()
        assert len(result) == 1
        conn.close()


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

            @always_comb
            def code():
                if sel:
                    out = 0
                else:
                    for i in range(width):
                        out[i] = 1
            self.add_always(code)

    mod = Mod(4)
    with tempfile.TemporaryDirectory() as temp:
        debug_db = os.path.join(temp, "debug.db")
        filename = os.path.join(temp, "test.sv")
        verilog(mod, filename=filename, insert_debug_info=True,
                debug_db_filename=debug_db)
        conn = sqlite3.connect(debug_db)
        c = conn.cursor()
        c.execute("SELECT * FROM context_variable")
        variables = c.fetchall()
        assert len(variables) > 20
        conn.close()


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
        verilog(parent, filename=filename, insert_debug_info=True,
                debug_db_filename=debug_db)


def test_assert():
    from kratos import assert_
    mod = Generator("mod", True)
    in_ = mod.input("in", 1)
    out_ = mod.output("out", 1)

    @always_comb
    def code():
        # we introduce this bug on purpose
        out_ = in_ - 1
        assert_(out_ == in_)

    mod.add_always(code)
    with tempfile.TemporaryDirectory() as temp:
        debug_db = os.path.join(temp, "debug.db")
        filename = os.path.join(temp, "test.sv")
        verilog(mod, filename=filename, insert_debug_info=True,
                debug_db_filename=debug_db)
        with open(filename) as f:
            content = f.read()
            assert "assert (out == in) else" in content
        conn = sqlite3.connect(debug_db)
        c = conn.cursor()
        c.execute("SELECT * FROM breakpoint")
        lines = c.fetchall()
        assert len(lines) == 2
        # they are only one line apart
        assert abs(lines[0][3] - lines[1][3]) == 1
        conn.close()
    # once we remove the assertion, it should not be there
    _kratos.passes.remove_assertion(mod.internal_generator)
    src = verilog(mod)[0]["mod"]
    assert "assert" not in src


def test_wire():
    mod = Generator("mod", True)
    in_ = mod.input("in", 1)
    out_ = mod.output("out", 1)
    # context
    a = 1
    mod.wire(out_, in_)
    with tempfile.TemporaryDirectory() as temp:
        debug_db = os.path.join(temp, "debug.db")
        filename = os.path.join(temp, "test.sv")
        verilog(mod, filename=filename, insert_debug_info=True,
                debug_db_filename=debug_db)
        conn = sqlite3.connect(debug_db)
        c = conn.cursor()
        c.execute("SELECT * FROM breakpoint")
        assert len(c.fetchall()) == 1
        c.execute("""SELECT variable.value FROM variable, context_variable
                     WHERE context_variable.name = ? AND context_variable.variable_id = variable.id""", "a")
        v = int(c.fetchone()[0])
        assert v == a
        conn.close()


def test_inst_id():
    def create_mod():
        m = Generator("mod", True)
        in_ = m.input("in", 1)
        out = m.output("out", 1)
        comb = m.combinational()
        comb.add_stmt(out.assign(in_))
        return m
    mod = Generator("parent", True)
    input_ = mod.input("in", 1)
    output = mod.output("out", 1)
    mods = [create_mod() for _ in range(2)]
    expr = None
    for i, m_ in enumerate(mods):
        mod.add_child("mod{0}".format(i), m_)
        mod.wire(input_, m_.ports["in"])
        if expr is None:
            expr = m_.ports["out"]
        else:
            expr = expr & m_.ports["out"]
    mod.wire(output, expr)

    with tempfile.TemporaryDirectory() as temp:
        debug_db = os.path.join(temp, "debug.db")
        verilog(mod, insert_debug_info=True, debug_db_filename=debug_db,
                optimize_passthrough=False)
        conn = sqlite3.connect(debug_db)
        c = conn.cursor()
        c.execute("SELECT * FROM instance")
        res = c.fetchall()
        assert len(res) == 3
        conn.close()


def test_empty():
    from kratos.debug import dump_external_database
    mod = Generator("mod", True)
    with tempfile.TemporaryDirectory() as temp:
        debug_db = os.path.join(temp, "debug.db")
        dump_external_database([mod], "mod", debug_db)


def test_nested_scope():
    from kratos import clog2
    mod = Generator("FindHighestBit", True)
    width = 4
    data = mod.input("data", width)
    h_bit = mod.output("h_bit", clog2(width))
    done = mod.var("done", 1)

    @always_comb
    def find_bit():
        done = 0
        h_bit = 0
        for i in range(width):
            if ~done:
                if data[i]:
                    done = 1
                    h_bit = i
    mod.add_always(find_bit, label="block")
    verilog(mod, insert_debug_info=True)
    block = mod.get_marked_stmt("block")
    last_if = block[-1]
    for i in range(len(last_if.then_[-1].then_)):
        stmt = last_if.then_[-1].then_[i]
        context = stmt.scope_context
        if len(context) > 0:
            assert "i" in context
            is_var, var = context["i"]
            assert not is_var
            assert var == "3"


def test_array_packed():
    from kratos import PackedStruct
    mod = Generator("mod", True)
    aa = mod.var("a", 2, size=(2, 4), packed=True)
    struct = PackedStruct("s", [("read", 16, False),
                                ("data", 16, False)])
    ss = mod.var_packed("s", struct)
    mod.add_stmt(aa.assign(4))
    setattr(mod, "sss", ss)
    mod.add_stmt(ss["read"].assign(0))
    mod.add_stmt(ss["data"].assign(1))

    with tempfile.TemporaryDirectory() as temp:
        debug_db = os.path.join(temp, "debug.db")
        verilog(mod, debug_db_filename=debug_db, insert_debug_info=True)
        conn = sqlite3.connect(debug_db)
        c = conn.cursor()
        c.execute("SELECT variable.value, generator_variable.name FROM variable, generator_variable WHERE variable.id = generator_variable.variable_id")
        vars_ = c.fetchall()
        c.execute("SELECT variable.value, context_variable.name FROM variable, context_variable WHERE variable.id = context_variable.variable_id")
        vars_ += c.fetchall()
        correct_struct, correct_array, correct_self = False, False, False
        for value, name in vars_:
            if value == "a[1][3]" and name == "aa.1.3":
                correct_array = True
            if value == "s.read" and name == "ss.read":
                correct_struct = True
            if "self.sss" in name:
                correct_self = True
        assert correct_array and correct_struct, correct_self
        conn.close()


def test_multiple_instance():
    class Mod(Generator):
        def __init__(self, width, param):
            super().__init__("child_{0}_{1}".format(width, param), True)
            in_ = self.input("child_in", width)
            out_ = self.output("child_out", width)

            @always_comb
            def code():
                out_ = 0
                for i in range(param):
                    out_ = in_ + param

            self.add_always(code)

    top = Generator("parent", True)
    top_in = top.input("in", 8)
    top_out = top.output("out", 8)
    children = []
    out_ports = []
    num_instance = 3
    for i in range(num_instance):
        child = Mod(8, i + 2)
        children.append(child)
    for i in range(num_instance):
        child = children[i]
        top.add_child("child_{0}".format(i), child,
                      child_in=top_in)
        out_ports.append(child.ports.child_out)

    top.wire(top_out, reduce_add(*out_ports))

    # testing code
    with tempfile.TemporaryDirectory() as temp:
        filename = os.path.join(temp, "test.sv")
        verilog(top, filename=filename, insert_debug_info=True, debug_fn_ln=True)
        # check the id and line info
        with open(filename) as f:
            content = f.read()
            assert ".KRATOS_INSTANCE_ID(32'h2))" in content
        # make sure that the line is mapped correctly
        with open(__file__) as f:
            lines = f.readlines()
            index = -1
            for i in range(len(lines)):
                if "out_ = in_ + param" in lines[i]:
                    index = i
                    break
            assert index != -1
        line_no = index + 1  # 1 offset for line number
        with open(filename + ".debug") as f:
            import json
            content = json.load(f)
        count = 0
        for _, entry in content.items():
            __, ln = entry[0]
            if ln == line_no:
                count += 1
        assert count == num_instance * (num_instance + 3) / 2


def get_line(line):
    with open(__file__) as f:
        lines = f.readlines()
        lines = [l.rstrip() for l in lines]
    return lines.index(line) + 1


def test_ssa_debug():
    mod = Generator("mod", debug=True)
    a = mod.var("a", 4)
    clk = mod.clock("clk")
    b = mod.var("b", 1)
    loop_size = 4

    @always_comb
    def logic1():
        a = 0
        if b:
            for i in range(loop_size):
                a = a + i

    @always_ff((posedge, clk))
    def logic2():
        if a == 1:
            b = 1
        else:
            b = 0

    mod.add_always(logic1, ssa_transform=True)
    mod.add_always(logic2)

    with tempfile.TemporaryDirectory() as temp:
        debug_db = os.path.join(temp, "debug.db")
        verilog(mod, insert_debug_info=True, debug_db_filename=debug_db, ssa_transform=True)
        # assert the line number tracking
        conn = sqlite3.connect(debug_db)
        c = conn.cursor()
        idx = get_line("                a = a + i")
        c.execute("SELECT * FROM breakpoint WHERE line_num=?", (idx,))
        result = c.fetchall()
        assert len(result) == loop_size
        assert "a_4" in result[0][-1]
        # check the context variable
        c.execute("SELECT * FROM context_variable WHERE context_variable.name = 'i'")
        result = c.fetchall()
        assert len(result) == loop_size
        # check the assignment
        c.execute("SELECT * FROM assignment WHERE assignment.name = 'a'")
        result = c.fetchall()
        assert result[0][1] == "a_0"
        assert len(result) == (loop_size + 2)
        c.execute("SELECT * FROM assignment WHERE assignment.name = 'b'")
        result = c.fetchall()
        assert len(result) == 2
        conn.close()


if __name__ == "__main__":
    test_ssa_debug()
