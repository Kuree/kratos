import _kratos
from kratos import Generator, Event, always_comb


def test_event_extraction():
    mod = Generator("mod")
    event = Event("test1/event")

    a = mod.var("a", 1)
    b = mod.var("b", 1)
    c = mod.var("c", 2)
    d = mod.var("d", 2)

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

    mod.add_always(if_stmt)
    mod.add_always(switch_if)

    # convert to if to switch
    _kratos.passes.transform_if_to_case(mod.internal_generator)
    # extract out the enable condition
    info = _kratos.extract_event_fire_condition(mod.internal_generator)


if __name__ == "__main__":
    test_event_extraction()
