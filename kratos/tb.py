import _kratos
from .generator import Generator, transform_stmt_block, \
    InitialCodeBlock, VarProxy, StatementBlockType
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


def delay(num, stmt):
    assert isinstance(stmt, _kratos.AssignStmt)
    stmt.delay = num
    return stmt


class TestBench:
    # disable pytest collection
    __test__ = False

    def __init__(self, top_name: str = "TOP"):
        self.__tb = _kratos.TestBench(Generator.get_context(), top_name)
        self.__child_generator = {}
        self.debug = False
        self.internal_generator = self.__tb.top()

        # proxy
        self.vars = VarProxy(self)

    def var(self, name, width, size: int = 1, is_signed: bool = False):
        return self.__tb.var(name, width, size, is_signed)

    def add_child_generator(self, instance_name: str, generator: Generator):
        assert instance_name not in self.__child_generator
        self.__child_generator[instance_name] = generator
        self.__tb.add_child_generator(instance_name,
                                      generator.internal_generator)

    add_child = add_child_generator

    def codegen(self):
        return self.__tb.codegen()

    def add_stmt(self, stmt):
        if not isinstance(stmt, _kratos.Stmt):
            self.__tb.add_stmt(stmt.stmt())
        else:
            self.__tb.add_stmt(stmt)

    def wire(self, var1, var2):
        self.__tb.wire(var1, var2)

    def initial(self):
        return self.__tb.initial()

    def add_always(self, fn, comment=""):
        block_type, raw_sensitives, stmts = transform_stmt_block(self, fn)
        if block_type != StatementBlockType.Initial:
            raise NotImplementedError(
                "Only initial supported in test bench")
        if block_type == StatementBlockType.Combinational:
            node = None
            pass
        elif block_type == StatementBlockType.Initial:
            # it's a initial block
            init = InitialCodeBlock(self)
            for stmt in stmts:
                init.add_stmt(stmt)
            node = init
        else:
            node = None
        if comment:
            node.comment = comment

    add_code = add_always

    def property(self, property_name: str, sequence):
        return self.__tb.property(property_name, sequence)
