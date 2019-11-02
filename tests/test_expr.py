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
    assert assign.left == a
    assert assign.right == b


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


def test_md_array():
    mod = Generator("mod")
    a = mod.var("a", 16, size=(4, 2), packed=True)
    b = mod.var("b", 16, size=(4, 2), packed=True)
    mod.wire(b, a)
    src = verilog(mod)["mod"]
    assert "logic [3:0][1:0][15:0] a;" in src


if __name__ == "__main__":
    test_md_array()

