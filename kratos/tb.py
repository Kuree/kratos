import _kratos
from .generator import Generator
from _kratos import get_fn_ln


def assert_(expr):
    if isinstance(expr, _kratos.Var):
        stmt = _kratos.AssertValueStmt(expr)
    else:
        assert isinstance(expr, _kratos.Property)
        expr.action = _kratos.PropertyAction.Assert
        stmt = _kratos.AssertPropertyStmt(expr)
    if expr.generator.debug:
        stmt.add_fn_ln(get_fn_ln())
    return stmt


def assume(prop):
    prop.action = _kratos.PropertyAction.Assume
    stmt = _kratos.AssertPropertyStmt(prop)
    return stmt


def cover(prop):
    prop.action = _kratos.PropertyAction.Cover
    stmt = _kratos.AssertPropertyStmt(prop)
    return stmt


def delay(num, stmt, lhs=True):
    event = _kratos.EventControl(num)
    if stmt is None:
        stmt = _kratos.EventDelayStmt(event)
    else:
        assert isinstance(stmt, _kratos.AssignStmt)
        event.delay_side = _kratos.DelaySide.Left if lhs else _kratos.DelaySide.Right
        stmt.delay = event
    return stmt


class TestBench(Generator):
    # disable pytest collection
    __test__ = False

    def __init__(self, top_name: str = "TOP"):
        gen = Generator.get_context().testbench(top_name)
        super(TestBench, self).__init__(top_name, internal_generator=gen)
