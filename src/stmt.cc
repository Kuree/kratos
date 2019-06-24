#include "stmt.hh"
#include <algorithm>
#include "fmt/format.h"
#include "generator.hh"
#include "port.hh"

using fmt::format;
using std::move;
using std::runtime_error;

ASTNode *Stmt::parent() { return parent_; }

AssignStmt::AssignStmt(const std::shared_ptr<Var> &left, const std::shared_ptr<Var> &right)
    : AssignStmt(left, right, AssignmentType::Undefined) {}

AssignStmt::AssignStmt(const std::shared_ptr<Var> &left, const std::shared_ptr<Var> &right,
                       AssignmentType type)
    : Stmt(StatementType ::Assign), left_(left), right_(right), assign_type_(type) {
    if (left == nullptr) throw ::runtime_error("left hand side is empty");
    if (right == nullptr) throw ::runtime_error("right hand side is empty");
    // check for sign
    if (left->is_signed != right->is_signed) {
        throw ::runtime_error(
            ::format("left ({0})'s sign does not match with right ({1}). {2} <- {3}", left->name,
                     right->name, left->is_signed, right->is_signed));
    }
    // check for width
    if (left->width != right->width) {
        throw ::runtime_error(
            ::format("left ({0})'s width does not match with right ({1}). {2} <- {3}", left->name,
                     right->name, left->width, right->width));
    }
}

bool AssignStmt::equal(const std::shared_ptr<AssignStmt> &stmt) const {
    return left_ == stmt->left_ && right_ == stmt->right_;
}

bool AssignStmt::operator==(const AssignStmt &stmt) const {
    return left_ == stmt.left_ && right_ == stmt.right_;
}

ASTNode *AssignStmt::get_child(uint64_t index) {
    if (index == 0)
        return left_.get();
    else if (index == 1)
        return right_.get();
    else
        return nullptr;
}

IfStmt::IfStmt(std::shared_ptr<Var> predicate)
    : Stmt(StatementType::If), predicate_(::move(predicate)) {}

void IfStmt::add_then_stmt(const std::shared_ptr<Stmt> &stmt) {
    if (stmt->type() == StatementType::Block)
        throw ::runtime_error("cannot add statement block to the if statement body");
    then_body_.emplace_back(stmt);
}

void IfStmt::add_else_stmt(const std::shared_ptr<Stmt> &stmt) {
    if (stmt->type() == StatementType::Block)
        throw ::runtime_error("cannot add statement block to the if statement body");
    else_body_.emplace_back(stmt);
}

ASTNode *IfStmt::get_child(uint64_t index) {
    if (index == 0)
        return predicate_.get();
    else if (index < then_body_.size() + 1)
        return then_body_[index - 1].get();
    else if (index < then_body_.size() + else_body_.size() + 1)
        return else_body_[index - then_body_.size() - 1].get();
    else
        return nullptr;
}

StmtBlock::StmtBlock(StatementBlockType type) : Stmt(StatementType::Block), block_type_(type) {}

void StmtBlock::add_statement(std::shared_ptr<Stmt> stmt) {
    // it cannot add another block stmt
    if (stmt->type() == StatementType::Block) {
        throw ::runtime_error("cannot add statement block to another statement block");
    }
    if (std::find(stmts_.begin(), stmts_.end(), stmt) != stmts_.end()) {
        throw ::runtime_error("cannot add the same block to the block list");
    }
    // if it is an assign statement, check the assignment as well
    if (stmt->type() == StatementType::Assign) {
        auto assign_stmt = stmt->as<AssignStmt>();
        if (assign_stmt->assign_type() == AssignmentType::Undefined) {
            assign_stmt->set_assign_type(block_type() == StatementBlockType::Combinational
                                             ? AssignmentType::Blocking
                                             : AssignmentType::NonBlocking);
        } else if (assign_stmt->assign_type() == AssignmentType::NonBlocking &&
                   block_type_ == StatementBlockType::Combinational) {
            throw ::runtime_error("cannot add blocking assignment to a sequential block");
        } else if (assign_stmt->assign_type() == AssignmentType::Blocking &&
                   block_type_ == StatementBlockType::Sequential) {
            throw ::runtime_error("cannot add non-blocking assignment to a combinational block");
        }
    }
    stmts_.emplace_back(stmt);
}

void SequentialStmtBlock::add_condition(
    const std::pair<BlockEdgeType, std::shared_ptr<Var>> &condition) {
    // notice that the condition variable cannot be used as a condition
    // for now we only allow Port (clk and reset) type to use as conditions
    if (condition.second->type() != VarType::PortIO)
        throw ::runtime_error("only ports are allowed for sequential block condition.");
    const auto &port = condition.second->as<Port>();
    if (port->port_type() != PortType::AsyncReset && port->port_type() != PortType::Clock) {
        throw ::runtime_error(
            "only clock and async reset allowed to use as sequential block condition");
    }
    conditions_.emplace(condition);
}

SwitchStmt::SwitchStmt(const std::shared_ptr<Var> &target)
    : Stmt(StatementType::Switch), target_(target) {
    // we don't allow const target
    if (target->type() == VarType::ConstValue)
        throw ::runtime_error(::format("switch target cannot be const value {0}", target->name));
}

void SwitchStmt::add_switch_case(const std::shared_ptr<Const> &switch_case,
                                 const std::shared_ptr<Stmt> &stmt) {
    // we want to make sure that we don't have duplicated switch case
    for (const auto &[case_var, body] : body_) {
        const auto &case_const = case_var->as<Const>();
        if (case_const->value() == switch_case->value())
            throw ::runtime_error(
                ::format("{0} already exists in the case statement", case_const->value()));
    }
    body_.emplace(switch_case, stmt);
}

ASTNode *SwitchStmt::get_child(uint64_t index) {
    if (index == 0) {
        return target_.get();
    } else if (index < body_.size() + 1) {
        // this is not an efficient way for doing this
        std::vector<std::shared_ptr<Const>> keys;
        for (const auto &[key, value] : body_) keys.emplace_back(key);
        auto const key = keys[index - 1];
        return body_[key].get();
    } else {
        return nullptr;
    }
}

ModuleInstantiationStmt::ModuleInstantiationStmt(Generator *target, Generator *parent)
    : Stmt(StatementType::ModuleInstantiation), target_(target), parent_(parent) {}