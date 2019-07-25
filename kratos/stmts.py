import _kratos
from .util import get_fn_ln


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
            self._stmt.add_then_stmt(stmt)
        return self

    def else_(self, *args: _kratos.Stmt):
        for stmt in args:
            if self.__generator.debug:
                stmt.add_fn_ln(get_fn_ln())
            self._stmt.add_else_stmt(stmt)

    def stmt(self):
        return self._stmt


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
            cond = self.__generator.constant(cond, self.__predicate.width,
                                             self.__predicate.signed)
        case = self._stmt.add_switch_case(cond, args)
        if self.__generator.debug:
            case.add_fn_ln(get_fn_ln())
        return self

    def stmt(self):
        return self._stmt


def switch_(predicate: _kratos.Var):
    return SwitchStmt(predicate)
