from kratos import Generator, Attribute


def test_wrapper_flatten_generator(check_gold):
    mod = Generator("mod")
    a = mod.input("a", 4, size=[3, 2])
    b = mod.output("b", 4, size=[3, 2])
    attr = Attribute()
    attr.value_str = "a"
    a.add_attribute(attr)
    mod.wire(a, b)
    from _kratos import create_wrapper_flatten
    wrapper = create_wrapper_flatten(mod.internal_generator, "wrapper")
    wrapper = Generator(wrapper.name, internal_generator=wrapper)
    check_gold(wrapper, gold_name="test_wrapper_flatten_generator",
               optimize_passthrough=False)
    a_0_0 = wrapper.ports.a_0_0
    attrs = a_0_0.find_attribute(lambda x: x.value_str == "a")
    assert len(attrs) == 1
