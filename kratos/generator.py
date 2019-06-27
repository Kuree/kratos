import enum
from _kratos import Generator as _Generator, Context as _Context, \
    PortDirection as _PortDirection, PortType as _PortType, \
    BlockEdgeType as _BlockEdgeType, \
    SequentialStmtBlock as _SequentialStmtBlock, \
    CombinationalStmtBlock as _CombinationalStmtBlock, \
    StatementBlockType as _StatementBlockType


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


class CodeBlock:
    def __init__(self, block_type: StatementBlockType):
        self.block_type = block_type
        if block_type == StatementBlockType.Combinational:
            self._block = _CombinationalStmtBlock()
        else:
            self._block = _SequentialStmtBlock()


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

    def var(self, name: str, width: int, signed: bool = False):
        return self.__generator.var(name, width, signed)

    def port(self, name: str, width: int, direction: PortDirection,
             port_type: PortType = PortType.Data,
             signed: bool = False):
        return self.__generator.port(direction.value, name, width,
                                     port_type.value, signed)
