from .generator import Generator, PortType, PortDirection, BlockEdgeType, \
    always, initial, CombinationalCodeBlock, SequentialCodeBlock, \
    set_global_debug

from .passes import Attribute, verilog
from .util import clog2, reduce_add, reduce_and, reduce_mul, reduce_or,\
    concat, zext, mux, ternary, signed, const, comment, unsigned

from .ports import PortBundle
from .tb import TestBench, assert_, delay
from .debug import enable_runtime_debug
from .pyast import add_scope_context

# directly import from the underlying C++ binding
from _kratos.util import is_valid_verilog
from _kratos.exception import VarException, StmtException
from _kratos.passes import IRVisitor as IRVisitor
from _kratos import PackedStruct, Port, Var, AssignmentType
from _kratos import Sequence
from _kratos import DebugDataBase
from .stmts import IfStmt, SwitchStmt, if_, switch_

# FSMs
from _kratos import FSM, FSMState

posedge = BlockEdgeType.Posedge
negedge = BlockEdgeType.Negedge

__all__ = ["Generator", "PortType", "PortDirection", "BlockEdgeType", "always",
           "verilog", "const", "is_valid_verilog", "VarException",
           "StmtException", "IRVisitor", "FSM", "FSMState", "initial",
           "Sequence", "TestBench", "assert_", "delay", "enable_runtime_debug"]

__all__ += ["CombinationalCodeBlock", "SequentialCodeBlock", "SwitchStmt",
            "PackedStruct", "Port", "Var", "IfStmt", "AssignmentType",
            "if_", "switch_", "Attribute", "PortBundle", "DebugDataBase",
            "add_scope_context", "set_global_debug"]

# utils
__all__ += ["clog2", "reduce_add", "reduce_and", "reduce_mul", "reduce_or",
            "concat", "zext", "comment", "signed", "unsigned"]

# type aliasing
__all__ += ["BlockEdgeType", "posedge", "negedge", "mux", "ternary"]
