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


if __name__ == "__main__":
    test_event_extraction()
