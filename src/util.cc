#include "expr.hh"
#include "fmt/format.h"
#include "port.hh"
#include "stmt.hh"
#include "generator.hh"
#include "except.hh"

#include "slang/compilation/Compilation.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/text/SourceManager.h"

namespace kratos {

std::string ExprOpStr(ExprOp op) {
    switch (op) {
        case UInvert:
            return "~";
        case UMinus:
        case Minus:
            return "-";
        case UPlus:
        case Add:
            return "+";
        case Divide:
            return "/";
        case Multiply:
            return "*";
        case Mod:
            return "%";
        case LogicalShiftRight:
            return ">>";
        case SignedShiftRight:
            return ">>>";
        case ShiftLeft:
            return "<<";
        case Or:
            return "|";
        case And:
            return "&";
        case Xor:
            return "^";
        case LessThan:
            return "<";
        case GreaterThan:
            return ">";
        case LessEqThan:
            return "<=";
        case GreaterEqThan:
            return ">=";
        case Eq:
            return "==";
        case Neq:
            return "!=";
        default:
            throw std::runtime_error("unable to find op");
    }
}

std::string var_type_to_string(VarType type) {
    if (type == VarType::Base)
        return "Base";
    else if (type == VarType::PortIO)
        return "Port";
    else if (type == VarType::Expression)
        return "Expression";
    else if (type == VarType::ConstValue)
        return "Const";
    else
        return "Slice";
}

std::string ast_type_to_string(IRNodeKind kind) {
    if (kind == IRNodeKind::StmtKind)
        return "Statement";
    else if (kind == IRNodeKind::VarKind)
        return "Variable";
    else
        return "Generator";
}

std::string assign_type_to_str(AssignmentType type) {
    if (type == AssignmentType::Blocking)
        return "blocking";
    else if (type == AssignmentType::NonBlocking)
        return "non-blocking";
    else
        return "undefined";
}

std::string port_dir_to_str(PortDirection direction) {
    if (direction == PortDirection::In) {
        return "input";
    } else if (direction == PortDirection::Out) {
        return "output";
    } else {
        return "inout";
    }
}

bool is_valid_verilog(const std::string &src) {
    slang::SourceManager source_manager;
    slang::Compilation compilation;
    auto tree = slang::SyntaxTree::fromText(src, source_manager);
    compilation.addSyntaxTree(tree);
    auto &diagnostics = compilation.getParseDiagnostics();
    return diagnostics.empty();
}

std::string port_type_to_str(PortType type) {
    switch (type) {
        case PortType::Reset:
            return "reset";
        case PortType::Data:
            return "data";
        case PortType ::ClockEnable:
            return "clk_en";
        case PortType ::Clock:
            return "clk";
        case PortType ::AsyncReset:
            return "async_reset";
        default:
            throw std::runtime_error("unknown port type");
    }
}

void remove_stmt_from_parent(const std::shared_ptr<Stmt> &stmt) {
    auto parent = stmt->parent();
    if (!parent)
        return;
    if (parent->ir_node_kind() == IRNodeKind::GeneratorKind) {
        auto p = dynamic_cast<Generator*>(parent);
        p->remove_stmt(stmt);
    } else {
        if (parent->ir_node_kind() != IRNodeKind::StmtKind) {
            throw StmtException("Internal error", {stmt.get()});
        }
        auto p_stmt = dynamic_cast<Stmt*>(parent);
        if (p_stmt->type() == StatementType::Switch) {
            auto p = dynamic_cast<SwitchStmt*>(p_stmt);
            p->remove_stmt(stmt);
        } else if (p_stmt->type() == StatementType::If) {
            auto  p = dynamic_cast<IfStmt*>(p_stmt);
            p->remove_stmt(stmt);
        } else {
            if (p_stmt->type() != StatementType::Block) {
                throw StmtException("Internal error", {stmt.get()});
            }
            auto p = dynamic_cast<StmtBlock*>(p_stmt);
            p->remove_stmt(stmt);
        }
    }
}

}