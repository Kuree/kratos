from kratos import Generator, signed, unsigned, verilog
from kratos.util import reduce_or, Const, const
import _kratos.exception


def test_expr():
    mod = Generator("mod")
    a = mod.var("a", 2)
    b = mod.var("b", 2)
    expr = a + b
    assert str(expr) == "a + b"


def test_slice():
    mod = Generator("mod")
    a = mod.var("a", 2)
    b = a[0]
    assert b.width == 1
    b = a[1, 0]
    assert b.width == 2
    assert str(b) == "a[1:0]"


def test_assign():
    mod = Generator("mod")
    a = mod.var("a", 2)
    b = mod.var("b", 2)
    assign = a.assign(b)
    assert id(assign.left) == id(a)
    assert id(assign.right) == id(b)


def test_signed():
    mod = Generator("mod")
    a = mod.var("a", 2)
    c = signed(a)
    assert str(c) == "signed'(a)"


def test_unsigned():
    mod = Generator("mod")
    a = mod.var("a", 2, is_signed=True)
    c = unsigned(a)
    assert str(c) == "unsigned'(a)"


def test_reduce_or():
    mod = Generator("mod")
    a = mod.var("a", 2)
    b = mod.var("b", 2)
    expr = reduce_or(a, b)
    assert str(expr) == "a | b"
    assert str(reduce_or(a)) == "a"


def test_const():
    a = Const[4](2)
    b = const(2, 4)
    assert str(a) == str(b)
    assert str(a) == "4'h2"


def test_width():
    mod = Generator("mod", True)
    a = mod.var("a", 1)
    a.width = 2
    file_names = list(a.fn_name_ln)
    assert len(file_names) == 2
    assert file_names[0][0] == file_names[1][0]
    assert abs(file_names[0][1] - file_names[1][1]) == 1


def test_slice_same():
    mod = Generator("mod")
    a = mod.var("a", 2, size=2)
    b = a[1, 1]
    assert str(b) == "a[1]"


def test_explicit_array():
    mod = Generator("mod")
    a = mod.var("a", 2, explicit_array=True, packed=True)
    b = a[0, 0]
    assert b.width == 2
    c = mod.var("c", 2, explicit_array=True, packed=True)
    d = mod.var("d", 1)
    e = mod.var("e", 2)
    mod.wire(c, a)
    mod.wire(e, a[d])
    src = verilog(mod)["mod"]
    assert "logic [0:0][1:0] a" in src


def test_neq():
    mod = Generator("mod")
    a = mod.var("a", 2)
    b = a != 2
    assert str(b) == "a != 2'h2"


def test_nested_ternary():
    from kratos import mux
    mod = Generator("mod")
    a = mod.var("a", 1)
    b = mod.var("b", 1)
    c = a + mux(a, a, b)
    assert str(c) == "a + (a ? a: b)"


def test_packed_unpacked():
    import _kratos
    mod = Generator("mod")
    a = mod.var("a", 2, size=2, packed=True)
    b = mod.var("b", 2, size=2)
    c = const(2, 4)
    d = mod.var("d", 4, explicit_array=True)
    try:
        a.assign(b)
        assert False
    except _kratos.exception.StmtException:
        assert True
    a.assign(4)
    try:
        b.assign(c)
        assert False
    except _kratos.exception.StmtException:
        assert True
    try:
        d.assign(a)
        assert False
    except _kratos.exception.StmtException:
        assert True

    # test for slices
    e = mod.var("e", 2, size=2, packed=True)
    e_0 = e[0]
    assert e_0.is_packed


def test_md_array():
    mod = Generator("mod")
    a = mod.var("a", 16, size=(4, 2), packed=True)
    b = mod.var("b", 16, size=(4, 2), packed=True)
    c = mod.var("c", 16, size=(2,), packed=True)
    mod.wire(b, a)
    mod.wire(c, a[1])
    src = verilog(mod)["mod"]
    assert "logic [3:0][1:0][15:0] a;" in src


def test_enum_cast():
    from kratos import enum
    e = enum("Type", ["a", "b"])
    mod = Generator("mod")
    var = mod.enum_var("v", e)
    casted = enum(const(1, 1), e)
    assert str(casted) == "Type'(1'h1)"
    var.assign(casted)


def test_bool_except():
    mod = Generator("mod")
    a = mod.var("a", 1)
    try:
        _ = not a
        assert False
    except _kratos.exception.InvalidConversionException:
        assert True


def test_single_concat():
    from kratos import concat
    mod = Generator("mod")
    a = mod.var("a", 1)
    r = concat([a])
    assert id(r) == id(a)


def test_resize():
    from kratos import resize
    mod = Generator("mod")
    a = mod.var("a", 1)
    b = resize(a, 16)
    assert b.width == 16
    assert str(b) == "16'(a)"


def test_power():
    mod = Generator("mod")
    a = mod.var("a", 5)
    b = 2 ** a
    assert str(b) == "5'h2 ** a"


def test_lshift():
    mod = Generator("mod")
    a = mod.var("a", 5)
    b = mod.var("b", 5)
    c = a << b
    assert str(c) == "a << b"


def test_big_num():
    from kratos import const
    a = const(2 ** 100, 120)
    assert a.is_bignum
    s = str(a)
    assert s == "120'h10000000000000000000000000"
    b = const(1, 120)
    assert not b.is_bignum


def test_var_slice_param():
    mod = Generator("mod")
    a = mod.parameter("a", initial_value=10)
    b = mod.var("b", a, size=4)
    c = b[0]
    assert c.width == 10
    a.value = 12
    assert b.width == 12
    assert c.width == 12


def test_concat_assign():
    from kratos import concat
    from _kratos.exception import VarException
    mod = Generator("mod")
    a = mod.var("a", 4)
    b = mod.var("b", 4)
    c = mod.var("c", 8)
    concat(a, b).assign(c)
    try:
        (a + b).assign(c)
        assert False
    except VarException:
        pass


def test_resize_const():
    from kratos import resize
    a = resize(0, 2)
    assert str(a) == "2'h0"
    b = resize(2, 4)
    assert str(b) == "4'h2"
    c = resize(-1, 2)
    assert str(c) == "-2'h1"


if __name__ == "__main__":
    test_resize_const()
