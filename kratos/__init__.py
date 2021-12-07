from .generator import Generator, PortType, PortDirection, BlockEdgeType, \
    initial, final, CombinationalCodeBlock, SequentialCodeBlock, \
    set_global_debug, enum, always_comb, always_ff, always_latch, has_enum

from .passes import Attribute, verilog, clear_context
from .util import clog2, reduce_add, reduce_and, reduce_mul, reduce_or, \
    concat, ext, mux, ternary, signed, const, comment, unsigned, create_stub, \
    resize, clock_en

from .ports import PortBundle
from .tb import TestBench, assert_, delay, assume, cover
from .debug import enable_runtime_debug
from .pyast import add_scope_context
from .sim import Simulator

# directly import from the underlying C++ binding
from _kratos.util import is_valid_verilog
from _kratos.exception import VarException, StmtException
from _kratos.passes import IRVisitor as IRVisitor
from _kratos import PackedStruct, Port, Var, AssignmentType, VarSlice, \
    VarVarSlice
from _kratos import Sequence
from _kratos import DebugDataBase
from .stmts import IfStmt, SwitchStmt, if_, switch_, RawStringStmt
from _kratos import Interface
from _kratos import PropertyAction, ParamType
from _kratos import Event, Transaction

# FSMs
from _kratos import FSM, FSMState

# fault
# TODO fix this namespace
from _kratos.fault import SimulationRun, FaultAnalyzer,\
    parse_verilator_coverage, parse_icc_coverage

posedge = BlockEdgeType.Posedge
negedge = BlockEdgeType.Negedge

__all__ = ["Generator", "PortType", "PortDirection", "BlockEdgeType",
           "verilog", "const", "is_valid_verilog", "VarException",
           "StmtException", "IRVisitor", "FSM", "FSMState", "initial", "final",
           "Sequence", "TestBench", "assert_", "delay", "enable_runtime_debug",
           "enum", "clear_context", "always_comb", "always_ff", "always_latch",
           "has_enum"]

__all__ += ["CombinationalCodeBlock", "SequentialCodeBlock", "SwitchStmt",
            "PackedStruct", "Port", "Var", "IfStmt", "AssignmentType",
            "if_", "switch_", "Attribute", "PortBundle", "DebugDataBase",
            "add_scope_context", "set_global_debug", "Interface", "VarSlice",
            "VarVarSlice", "ParamType", "Event", "Transaction"]

# utils
__all__ += ["clog2", "reduce_add", "reduce_and", "reduce_mul", "reduce_or",
            "concat", "ext", "comment", "signed", "unsigned", "create_stub",
            "resize"]

# type aliasing
__all__ += ["BlockEdgeType", "posedge", "negedge", "mux", "ternary"]
