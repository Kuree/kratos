import enum
from .pyast import transform_stmt_block, get_fn_ln
import _kratos
from typing import List, Dict


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
    __inspect_frame_depth: int = 2

    def __init__(self, name: str, debug: bool = False,
                 ):
        self.__generator = self.__context.generator(name)
        self.__child_generator: Dict[str, Generator] = {}

        self.debug = debug

        if debug:
            fn, ln = get_fn_ln(Generator.__inspect_frame_depth)
            self.__generator.add_fn_ln((fn, ln))

    def __getitem__(self, instance_name: str):
        assert instance_name in self.__child_generator, \
            f"{instance_name} does not exist in {self.instance_name}"
        return self.__child_generator[instance_name]

    def __setitem__(self, instance_name: str, generator: "Generator"):
        if instance_name in self.__child_generator:
            raise Exception(
                f"{instance_name} already exists in {self.instance_name}")
        assert isinstance(generator,
                          Generator), "generator is not a Generator instance"

        self.__child_generator[instance_name] = generator
        self.__generator.add_child_generator(generator.__generator,
                                             False)

    @property
    def name(self):
        return self.__generator.name

    @name.setter
    def name(self, name: str):
        self.__generator.name = name

    @property
    def instance_name(self):
        return self.__generator.name

    @instance_name.setter
    def instance_name(self, name: str):
        self.__generator.instance_name = name

    @property
    def is_stub(self):
        return self.__generator.is_stub()

    @is_stub.setter
    def is_stub(self, value: bool):
        self.__generator.set_is_stub(value)

    @property
    def external(self):
        return self.__generator.external()

    @external.setter
    def external(self, value: bool):
        self.__generator.set_external(value)

    @property
    def debug(self):
        return self.__generator.debug

    @debug.setter
    def debug(self, value):
        self.__generator.debug = value

    def var(self, name: str, width: int,
            is_signed: bool = False) -> _kratos.Var:
        v = self.__generator.var(name, width, is_signed)
        if self.debug:
            fn, ln = get_fn_ln()
            v.add_fn_ln((fn, ln))
        return v

    def port(self, name: str, width: int, direction: PortDirection,
             port_type: PortType = PortType.Data,
             is_signed: bool = False) -> _kratos.Port:
        p = self.__generator.port(direction.value, name, width,
                                  port_type.value, is_signed)
        if self.debug:
            fn, ln = get_fn_ln()
            p.add_fn_ln((fn, ln))
        return p

    def get_var(self, name):
        return self.__generator.get_var(name)

    def const(self, value: int, width: int, signed: bool = False):
        return self.__generator.constant(value, width, signed)

    @property
    def internal_generator(self):
        return self.__generator

    def add_code(self, fn):
        raw_sensitives, stmts = transform_stmt_block(self, fn, self.debug)
        if len(raw_sensitives) == 0:
            # it's a combinational block
            comb = CombinationalCodeBlock(self)
            for stmt in stmts:
                comb.add_stmt(stmt)
        else:
            sensitivity_list = []
            for edge, var_name in raw_sensitives:
                edge = BlockEdgeType[edge]
                var = self.internal_generator.get_var(var_name)
                sensitivity_list.append((edge, var))
            seq = SequentialCodeBlock(self, sensitivity_list)
            for stmt in stmts:
                seq.add_stmt(stmt)

    def __assign(self, var_from, var_to):
        stmt = var_from.assign(var_to, _kratos.AssignmentType.Blocking)
        self.add_stmt(stmt)
        return stmt

    def wire(self, var_to, var_from):
        # this is a top level direct wire assignment
        # notice that we can figure out the direction automatically if
        # both of them are ports
        if isinstance(var_to, _kratos.Port) and isinstance(var_from,
                                                           _kratos.Port):
            stmt = self.__generator.wire_ports(var_to, var_from)
        else:
            stmt = self.__assign(var_to, var_from)

        if self.debug:
            fn, ln = get_fn_ln(2)
            stmt.add_fn_ln((fn, ln))

    def add_stmt(self, stmt):
        self.__generator.add_stmt(stmt)

    def add_child_generator(self, instance_name: str, generator: "Generator"):
        self[instance_name] = generator

    @staticmethod
    def clear_context():
        Generator.__context.clear()

    @staticmethod
    def get_context():
        return Generator.__context

    @staticmethod
    def from_verilog(top_name: str, src_file: str, lib_files: List[str],
                     port_mapping: Dict[str, PortType]):
        g = Generator("")
        _port_mapping = {}
        for name, _type in port_mapping.items():
            _port_mapping[name] = _type.value
        g.__generator = _kratos.Generator.from_verilog(Generator.__context,
                                                       src_file, top_name,
                                                       lib_files, _port_mapping)
        Generator.__context.add(g.__generator)
        return g

    def __contains__(self, generator: "Generator"):
        if not isinstance(generator, (Generator, _kratos.Generator)):
            return False
        elif isinstance(generator, Generator):
            return self.__generator.has_child_generator(generator.__generator)
        else:
            return self.__generator.has_child_generator(generator)


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


def verilog(generator: Generator, optimize_if: bool = True,
            optimize_passthrough: bool = True,
            optimize_fanout: bool = True):
    code_gen = _kratos.VerilogModule(generator.internal_generator)
    code_gen.run_passes(optimize_if, optimize_passthrough, optimize_fanout)
    src = code_gen.verilog_src()
    debug = code_gen.debug_info()
    if len(debug) > 0:
        return src, debug
    else:
        return src
