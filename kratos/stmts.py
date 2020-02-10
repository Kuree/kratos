import _kratos
from .util import const
from typing import Union, List
from _kratos import get_fn_ln


class IfStmt:
    def __init__(self, predicate: _kratos.Var):
        self._stmt = _kratos.IfStmt(predicate)
        self.__generator = predicate.generator
        if self.__generator.debug:
            self._stmt.add_fn_ln(get_fn_ln())

    def then_(self, *args: _kratos.Stmt):
        for stmt in args:
            if self.__generator.debug:
                stmt.add_fn_ln(get_fn_ln())
            if not isinstance(stmt, _kratos.Stmt):
                stmt = stmt.stmt()
            self._stmt.add_then_stmt(stmt)
        return self

    def else_(self, *args: _kratos.Stmt):
        for stmt in args:
            if self.__generator.debug:
                stmt.add_fn_ln(get_fn_ln())
            if not isinstance(stmt, _kratos.Stmt):
                stmt = stmt.stmt()
            self._stmt.add_else_stmt(stmt)
        return self

    def then_body(self):
        return self._stmt.then_body()

    def else_body(self):
        return self._stmt.else_body()

    def add_scope_variable(self, name, value, is_var=False, override=False):
        self._stmt.add_scope_variable(name, value, is_var, override)

    def stmt(self):
        return self._stmt

    def add_fn_ln(self, info):
        self._stmt.add_fn_ln(info)


def if_(predicate: _kratos.Var):
    return IfStmt(predicate)


class SwitchStmt:
    def __init__(self, predicate: _kratos.Var):
        self._stmt = _kratos.SwitchStmt(predicate)
        if predicate.generator.debug:
            self._stmt.add_fn_ln(get_fn_ln())
        self.__predicate = predicate
        self.__generator = predicate.generator

    def case_(self, cond: _kratos.Var, *args: _kratos.Stmt):
        if isinstance(cond, int):
            cond = const(cond, self.__predicate.width, self.__predicate.signed)
        case = None
        for stmt in args:
            if not isinstance(stmt, _kratos.Stmt):
                stmt = stmt.stmt()
            case = self._stmt.add_switch_case(cond, stmt)
        assert case is not None
        if self.__generator.debug:
            case.add_fn_ln(get_fn_ln())
        return self

    def stmt(self):
        return self._stmt

    def add_scope_variable(self, name, value, is_var=False, override=False):
        self._stmt.add_scope_variable(name, value, is_var, override)


def switch_(predicate: _kratos.Var):
    return SwitchStmt(predicate)


class RawStringStmt:
    def __init__(self, value: Union[str, List[str]]):
        self._stmt = _kratos.RawStringStmt(value)

    def stmt(self):
        return self._stmt
