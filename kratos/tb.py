import _kratos
from .generator import Generator, transform_stmt_block, CodeBlockType, \
    InitialCodeBlock, comment_node, VarProxy


def assert_(expr):
    return _kratos.AssertValueStmt(expr)


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
        self.vars = VarProxy(self.internal_generator)

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

    def add_code(self, fn, comment_str=""):
        block_type, raw_sensitives, stmts = transform_stmt_block(self, fn)
        if block_type != CodeBlockType.Initial:
            raise NotImplementedError(
                "Only initial supported in test bench")
        if block_type == CodeBlockType.Combinational:
            node = None
            pass
        elif block_type == CodeBlockType.Initial:
            # it's a initial block
            init = InitialCodeBlock(self)
            for stmt in stmts:
                init.add_stmt(stmt)
            node = init
        else:
            node = None
        if comment_str:
            comment_node(node, comment_str)

    def property(self, property_name: str, sequence):
        return self.__tb.property(property_name, sequence)
