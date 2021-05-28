import _kratos
from kratos import Generator, Event, always_comb, always_ff, posedge


def test_event_extraction():
    mod = Generator("mod")
    event = Event("test1/event1")
    event_ff = Event("test1/event2")

    a = mod.var("a", 1)
    b = mod.var("b", 1)
    c = mod.var("c", 2)
    d = mod.var("d", 2)
    clk = mod.clock("clk")

    @always_comb
    def if_stmt():
        if a:
            event({"a": a})
        else:
            if b:
                event(b=b)
            else:
                event(c=c)

    @always_comb
    def switch_if():
        # this will be turn into a switch statement
        if d == 0:
            event(a1=a)
        elif d == 1:
            event(a2=a)
        elif d == 2:
            event(a3=a)
        else:
            event(a4=a)

    @always_ff((posedge, clk))
    def if_seq():
        if a:
            event_ff(a5=a)

    mod.add_always(if_stmt)
    mod.add_always(switch_if)
    mod.add_always(if_seq)

    # convert to if to switch
    _kratos.passes.transform_if_to_case(mod.internal_generator)
    # extract out the enable condition
    info = _kratos.extract_event_fire_condition(mod.internal_generator)
    assert len(info) == 8
    # check every conditions
    # check seq
    ffs = [i for i in info if not i.combinational]
    assert len(ffs) == 1
    assert str(ffs[0].condition) == "a"
    assert str(ffs[0].fields["a5"]) == "a"
    # check switch conditions
    ffs = [i for i in info if "a4" in i.fields]
    assert len(ffs) == 1
    assert str(ffs[0].fields["a4"]) == "a"
    assert str(ffs[0].condition) == "d != (2'h0 || 2'h1 || 2'h2)"
    # check normal switch condition
    ffs = [i for i in info if "a3" in i.fields]
    assert len(ffs) == 1
    assert str(ffs[0].condition) == "d == 2'h2"
    # check out if statements
    ffs = [i for i in info if "c" in i.fields]
    assert len(ffs) == 1
    assert str(ffs[0].condition) == "(!b) && (!a)"


def test_event_actions():
    mod = Generator("mod")
    event = Event("test1/event1")

    a = mod.var("a", 1)
    b = mod.var("b", 1)

    @always_comb
    def code():
        event(a=a).starts("transaction1").matches(a=a)
        event(b=b).terminates("transaction1").matches(a=b)

    mod.add_always(code)
    info = _kratos.extract_event_fire_condition(mod.internal_generator)
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
    sig = mod.var("sig", 1)

    @always_comb
    def code():
        event(sig=sig)

    mod.add_always(code)
    info = _kratos.extract_event_fire_condition(mod.internal_generator)
    stmt = info[0].stmt
    fn_lns = stmt.fn_name_ln
    assert len(fn_lns) == 1
    with open(__file__) as f:
        lines = f.readlines()
    idx = lines.index("        event(sig=sig)\n")


if __name__ == "__main__":
    test_event_debug_fn_ln()
