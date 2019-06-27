from kratos import Generator


def test_generator():
    mods = []
    for i in range(10):
        mod = Generator("mod1", f"a{i}")
        mods.append(mod)

    for idx, mod in enumerate(mods):
        assert mod.name == "mod1"
        mod.name = f"new_mod{idx}"
        assert mod.name == f"new_mod{idx}"
