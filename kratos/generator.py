import enum
from typing import Tuple
from _kratos import Generator as _Generator, Context as _Context, \
    PortDirection as _PortDirection, PortType as _PortType, \
    BlockEdgeType as _BlockEdgeType, \
    SequentialStmtBlock as _SequentialStmtBlock, \
    CombinationalStmtBlock as _CombinationalStmtBlock, \
    StatementBlockType as _StatementBlockType, Var as _Var, Port as _Port


# this is a wrapper python class to interface with the underlying python
# binding
class PortDirection(enum.Enum):
    In = _PortDirection.In
    Out = _PortDirection.Out
    InOut = _PortDirection.InOut


class PortType(enum.Enum):
    Data = _PortType.Data
    Clock = _PortType.Clock
    AsyncReset = _PortType.AsyncReset
    ClockEnable = _PortType.ClockEnable
    Reset = _PortType.Reset


class BlockEdgeType(enum.Enum):
    Posedge = _BlockEdgeType.Posedge
    Negedge = _BlockEdgeType.Negedge


class StatementBlockType(enum.Enum):
    Combinational = _StatementBlockType.Combinational
    Sequential = _SequentialStmtBlock.Sequential


class IfStatement:
    def __init__(self, generator: "Generator", target, *args):
        self._generator = generator
        self._if = self._generator.internal_generator.if_stmt(target)
        for stmt in args:
            self._if.add_then_stmt(stmt)

    def else_(self, *args):
        for stmt in args:
            self._if.add_else_stmt(stmt)

    def stmt(self):
        return self._if


class CodeBlock:
    def __init__(self, generator: "Generator", block_type: StatementBlockType):
        self.block_type = block_type
        self._generator = generator
        if block_type == StatementBlockType.Combinational:
            self._block = generator.internal_generator.combinational()
        else:
            self._block = generator.internal_generator.sequential()

    def add_stmt(self, stmt):
        if "stmt" in stmt.__dict__:
            self._block.add_statement(stmt.stmt())
        else:
            self._block.add_statement(stmt)


class SequentialCodeBlock(CodeBlock):
    def __init__(self, generator: "Generator", fn, sensitivity_list):
        super().__init__(generator, StatementBlockType.Sequential)
        for cond, var in sensitivity_list:
            assert isinstance(cond, BlockEdgeType)
            assert isinstance(var, _Var)
            self._block.add_condition([cond.value, var])
        self.fn = fn


class CombinationalCodeBlock(CodeBlock):
    def __init__(self, generator: "Generator", fn):
        super().__init__(generator, StatementBlockType.Combinational)

        self.fn = fn


class Generator:
    __context = _Context()

    def __init__(self, name: str, instance_name: str):
        self.__generator = self.__context.generator(name)
        self.__generator.instance_name = instance_name

    @property
    def name(self):
        return self.__generator.name

    @name.setter
    def name(self, name: str):
        self.__generator.name = name

    def var(self, name: str, width: int, signed: bool = False) -> _Var:
        return self.__generator.var(name, width, signed)

    def port(self, name: str, width: int, direction: PortDirection,
             port_type: PortType = PortType.Data,
             signed: bool = False) -> _Port:
        return self.__generator.port(direction.value, name, width,
                                     port_type.value, signed)

    def if_(self, target, *args):
        return IfStatement(self, target, *args)

    @property
    def internal_generator(self):
        return self.__generator

    def add_seq(self, fn, sensitivity):
        pass

    def add_comb(self, fn):
        pass
