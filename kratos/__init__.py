from .generator import Generator, PortType, PortDirection, BlockEdgeType, \
    always, verilog, signed, CombinationalCodeBlock, SequentialCodeBlock

from .passes import Attribute
from .util import clog2

# directly import from the underlying C++ binding
from _kratos.util import is_valid_verilog
from _kratos.exception import VarException, StmtException
from _kratos.passes import IRVisitor as IRVisitor
from _kratos import PackedStruct, Port, Var, AssignmentType
from .stmts import IfStmt, SwitchStmt, if_, switch_

__all__ = ["Generator", "PortType", "PortDirection", "BlockEdgeType", "always",
           "verilog", "signed", "is_valid_verilog", "VarException",
           "StmtException", "IRVisitor"]

__all__ += ["CombinationalCodeBlock", "SequentialCodeBlock", "SwitchStmt",
            "PackedStruct", "Port", "Var", "IfStmt", "AssignmentType",
            "AssignStmt", "clog2", "if_", "switch_", "Attribute"]

