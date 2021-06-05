import _kratos
import sqlite3
import tempfile
import os
import json

from kratos import Generator, Event, always_comb, always_ff, posedge, Transaction, verilog


def test_event_extraction():
    mod = Generator("mod")
    event = Event("test1/event1")
    event_ff = Event("test1/event2")
    t = Transaction("test")

    a = mod.var("a", 1)
    b = mod.var("b", 1)
    c = mod.var("c", 2)
    d = mod.var("d", 2)
    clk = mod.clock("clk")

    @always_comb
    def if_stmt():
        if a:
            t @ event({"a": a})
        else:
            if b:
                t @ event(b=b)
            else:
                t @ event(c=c)

    @always_comb
    def switch_if():
        # this will be turn into a switch statement
        if d == 0:
            t @ event(a1=a)
        elif d == 1:
            t @ event(a2=a)
        elif d == 2:
            t @ event(a3=a)
        else:
            t @ event(a4=a)

    @always_ff((posedge, clk))
    def if_seq():
        if a:
            t @ event_ff(a5=a)

    mod.add_always(if_stmt)
    mod.add_always(switch_if)
    mod.add_always(if_seq)

    # convert to if to switch
    _kratos.passes.transform_if_to_case(mod.internal_generator)
    info = _kratos.extract_event_info(mod.internal_generator)
    assert len(info) == 8
    # check seq
    ffs = [i for i in info if not i.combinational]
    assert len(ffs) == 1
    assert str(ffs[0].fields["a5"]) == "a"
    # check switch
    ffs = [i for i in info if "a4" in i.fields]
    assert len(ffs) == 1
    assert str(ffs[0].fields["a4"]) == "a"
    ffs = [i for i in info if "a3" in i.fields]
    assert len(ffs) == 1
    # check out if statements
    ffs = [i for i in info if "c" in i.fields]
    assert len(ffs) == 1


def test_event_actions():
    mod = Generator("mod")
    event = Event("test1/event1")
    t = Transaction("transaction1")

    a = mod.var("a", 1)
    b = mod.var("b", 1)

    @always_comb
    def code():
        t @ event(a=a).matches(a=a).starts()
        t @ event(b=b).matches(a=b).terminates()

    mod.add_always(code)
    info = _kratos.extract_event_info(mod.internal_generator)
    assert len(info) == 2
    # check actions
    event1 = info[0]
    assert "a" in event1.fields
    stmt = event1.stmt
    assert str(stmt.match_values["a"]) == "a"
    assert event1.transaction == "transaction1"
    assert event1.type == _kratos.EventActionType.Start

    event2 = info[1]
    assert "b" in event2.fields
    stmt = event2.stmt
    assert str(stmt.match_values["a"]) == "b"
    assert event2.type == _kratos.EventActionType.End


def test_event_debug_fn_ln():
    mod = Generator("mod", debug=True)
    event = Event("event")
    t = Transaction("transaction")
    sig = mod.var("sig", 1)

    @always_comb
    def code():
        t @ event(sig=sig)

    mod.add_always(code)
    info = _kratos.extract_event_info(mod.internal_generator)
    stmt = info[0].stmt
    fn_lns = stmt.fn_name_ln
    assert len(fn_lns) == 1
    with open(__file__) as f:
        lines = f.readlines()
    idx = lines.index("        t @ event(sig=sig)\n")
    assert (idx + 1) == fn_lns[0][1]


def test_event_serialization():
    mod = Generator("mod", debug=True)
    event = Event("event")
    t = Transaction("transaction")
    a = mod.var("a", 8)
    b = mod.var("b", 1)
    in_ = mod.input("in", 4)
    out = mod.output("out", 4)
    clk = mod.clock("clk")

    # notice that in kratos we only limit
    @always_ff((posedge, clk))
    def code():
        if a == 0:
            out = in_ + 1
            t @ event(value1=a, value2=b).matches(value2=b).starts()
        elif a == 1:
            out = in_ + 2
            t @ event(value3=a, value4=b).matches(value2=b)
        else:
            out = in_
            t @ event(value1=a, value4=b).matches(value2=b).terminates()

    mod.add_always(code)

    with tempfile.TemporaryDirectory() as temp:
        db_filename = os.path.join(temp, "debug.db")
        verilog(mod, insert_debug_info=True, debug_db_filename=db_filename, contains_event=True)
        conn = sqlite3.connect(db_filename)
        c = conn.cursor()
        c.execute("SELECT * from breakpoint")
        result = c.fetchall()
        # we have 8 lines
        assert len(result) == 8
        event_last = result[-1]
        assert event_last[-2] == "(!(a == 8'h1)) && (!(a == 8'h0))"
        # test out the event table
        c.execute("SELECT * from event")
        result = c.fetchall()
        # 3 events
        assert len(result) == 3
        assert result[0][0] == "event"
        # fields
        fields = json.loads(result[0][3])
        assert fields["value1"] == "mod.a"
        matches = json.loads(result[0][4])
        assert matches["value2"] == "mod.b"
        conn.close()


if __name__ == "__main__":
    test_event_serialization()
