import enum
from .pyast import transform_stmt_block
import _kratos


# this is a wrapper python class to interface with the underlying python
# binding
class PortDirection(enum.Enum):
    In = _kratos.PortDirection.In
    Out = _kratos.PortDirection.Out
    InOut = _kratos.PortDirection.InOut


class PortType(enum.Enum):
    Data = _kratos.PortType.Data
    Clock = _kratos.PortType.Clock
    AsyncReset = _kratos.PortType.AsyncReset
    ClockEnable = _kratos.PortType.ClockEnable
    Reset = _kratos.PortType.Reset


class BlockEdgeType(enum.Enum):
    Posedge = _kratos.BlockEdgeType.Posedge
    Negedge = _kratos.BlockEdgeType.Negedge


class StatementBlockType(enum.Enum):
    Combinational = _kratos.StatementBlockType.Combinational
    Sequential = _kratos.StatementBlockType.Sequential


class CodeBlock:
    def __init__(self, generator: "Generator", block_type: StatementBlockType):
        self.block_type = block_type
        self._generator = generator
        if block_type == StatementBlockType.Combinational:
            self._block = generator.internal_generator.combinational()
        else:
            self._block = generator.internal_generator.sequential()

    def add_stmt(self, stmt):
        if hasattr(stmt, "stmt"):
            self._block.add_statement(stmt.stmt())
        else:
            self._block.add_statement(stmt)

    def stmt(self):
        return self._block


class SequentialCodeBlock(CodeBlock):
    def __init__(self, generator: "Generator", sensitivity_list):
        super().__init__(generator, StatementBlockType.Sequential)
        for cond, var in sensitivity_list:
            assert isinstance(cond, BlockEdgeType)
            assert isinstance(var, _kratos.Var)
            self._block.add_condition([cond.value, var])


class CombinationalCodeBlock(CodeBlock):
    def __init__(self, generator: "Generator"):
        super().__init__(generator, StatementBlockType.Combinational)


class Generator:
    __context = _kratos.Context()

    def __init__(self, name: str, instance_name: str):
        self.__generator = self.__context.generator(name)
        self.__generator.instance_name = instance_name

    @property
    def name(self):
        return self.__generator.name

    @name.setter
    def name(self, name: str):
        self.__generator.name = name

    def var(self, name: str, width: int, signed: bool = False) -> _kratos.Var:
        return self.__generator.var(name, width, signed)

    def port(self, name: str, width: int, direction: PortDirection,
             port_type: PortType = PortType.Data,
             signed: bool = False) -> _kratos.Port:
        return self.__generator.port(direction.value, name, width,
                                     port_type.value, signed)

    def get_var(self, name):
        return self.__generator.get_var(name)

    def const(self, value: int, width: int, signed: bool = False):
        return self.__generator.constant(value, width, signed)

    @property
    def internal_generator(self):
        return self.__generator

    def add_seq(self, fn):
        raw_sensitives, stmts = transform_stmt_block(self, fn, True)
        sensitivity_list = []
        for edge, var_name in raw_sensitives:
            edge = BlockEdgeType[edge]
            var = self.internal_generator.get_var(var_name)
            sensitivity_list.append((edge, var))
        seq = SequentialCodeBlock(self, sensitivity_list)
        for stmt in stmts:
            seq.add_stmt(stmt)

    def add_comb(self, fn):
        _, stmts = transform_stmt_block(self, fn, False)
        comb = CombinationalCodeBlock(self)
        for stmt in stmts:
            comb.add_stmt(stmt)

    @staticmethod
    def clear_context():
        Generator.__context.clear()


def always(sensitivity):
    for edge, var in sensitivity:
        assert isinstance(edge, BlockEdgeType)
        assert isinstance(var, str)

    def wrapper(fn):
        return fn
    return wrapper


def signed(var):
    assert isinstance(var, _kratos.Var)
    return var.signed_()


def verilog(generator: Generator):
    code_gen = _kratos.VerilogModule(generator.internal_generator)
    return code_gen.verilog_src()
