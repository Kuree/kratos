#include "stmt.hh"
#include <algorithm>
#include "except.hh"
#include "fmt/format.h"
#include "generator.hh"
#include "port.hh"

using fmt::format;
using std::move;
using std::runtime_error;

namespace kratos {

IRNode *Stmt::parent() { return parent_; }

AssignStmt::AssignStmt(const std::shared_ptr<Var> &left, const std::shared_ptr<Var> &right)
    : AssignStmt(left, right, AssignmentType::Undefined) {}

AssignStmt::AssignStmt(const std::shared_ptr<Var> &left, const std::shared_ptr<Var> &right,
                       AssignmentType type)
    : Stmt(StatementType ::Assign), left_(left), right_(right), assign_type_(type) {
    if (left == nullptr) throw ::runtime_error("left hand side is empty");
    if (right == nullptr) throw ::runtime_error("right hand side is empty");
    // check for sign
    if (left->is_signed != right->is_signed) {
        throw VarException(::format("left ({0})'s sign does not match with right ({1}). {2} <- {3}",
                                    left->name, right->name, left->is_signed, right->is_signed),
                           {left.get(), right.get()});
    }
    // check for width
    if (left->width != right->width) {
        throw VarException(
            ::format("left ({0})'s width does not match with right ({1}). {2} <- {3}", left->name,
                     right->name, left->width, right->width),
            {left.get(), right.get()});
    }
}

bool AssignStmt::equal(const std::shared_ptr<AssignStmt> &stmt) const {
    return left_ == stmt->left_ && right_ == stmt->right_;
}

bool AssignStmt::operator==(const AssignStmt &stmt) const {
    return left_ == stmt.left_ && right_ == stmt.right_;
}

IRNode *AssignStmt::get_child(uint64_t index) {
    if (index == 0)
        return left_.get();
    else if (index == 1)
        return right_.get();
    else
        return nullptr;
}

void AssignStmt::set_parent(kratos::IRNode *parent) {
    Stmt::set_parent(parent);
    // push the stmt into its sources
    right_->add_sink(as<AssignStmt>());
    left_->add_source(as<AssignStmt>());
}

IfStmt::IfStmt(std::shared_ptr<Var> predicate)
    : Stmt(StatementType::If), predicate_(::move(predicate)) {
    then_body_ = std::make_shared<ScopedStmtBlock>();
    else_body_ = std::make_shared<ScopedStmtBlock>();

    then_body_->set_parent(this);
    else_body_->set_parent(this);
}

void IfStmt::add_then_stmt(const std::shared_ptr<Stmt> &stmt) {
    if (stmt->type() == StatementType::Block)
        throw ::runtime_error("cannot add statement block to the if statement body");
    stmt->set_parent(this);
    then_body_->add_stmt(stmt);
}

void IfStmt::add_else_stmt(const std::shared_ptr<Stmt> &stmt) {
    if (stmt->type() == StatementType::Block)
        throw ::runtime_error("cannot add statement block to the if statement body");
    stmt->set_parent(this);
    else_body_->add_stmt(stmt);
}

void IfStmt::remove_then_stmt(const std::shared_ptr<kratos::Stmt> &stmt) {
    then_body_->remove_stmt(stmt);
}

void IfStmt::remove_else_stmt(const std::shared_ptr<kratos::Stmt> &stmt) {
    else_body_->remove_stmt(stmt);
}

void IfStmt::remove_stmt(const std::shared_ptr<kratos::Stmt> &stmt) {
    for (auto const &s : *then_body_) {
        if (s == stmt) {
            remove_then_stmt(stmt);
            return;
        }
    }
    for (auto const &s: *else_body_) {
        if (s == stmt) {
            remove_else_stmt(stmt);
            return;
        }
    }
}

IRNode *IfStmt::get_child(uint64_t index) {
    if (index == 0)
        return predicate_.get();
    else if (index == 1)
        return then_body_.get();
    else if (index == 2)
        return else_body_.get();
    else
        return nullptr;
}

StmtBlock::StmtBlock(StatementBlockType type) : Stmt(StatementType::Block), block_type_(type) {}

void StmtBlock::add_stmt(const std::shared_ptr<Stmt> &stmt) {
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
            // let the passes to figure this out
        } else if (assign_stmt->assign_type() == AssignmentType::NonBlocking &&
                   block_type_ == StatementBlockType::Combinational) {
            throw ::runtime_error("cannot add blocking assignment to a sequential block");
        } else if (assign_stmt->assign_type() == AssignmentType::Blocking &&
                   block_type_ == StatementBlockType::Sequential) {
            throw ::runtime_error("cannot add non-blocking assignment to a combinational block");
        }
    }
    stmt->set_parent(this);
    stmts_.emplace_back(stmt);
}

void StmtBlock::remove_stmt(const std::shared_ptr<kratos::Stmt> &stmt) {
    auto pos = std::find(stmts_.begin(), stmts_.end(), stmt);
    if (pos != stmts_.end())
        stmts_.erase(pos);
}

void StmtBlock::set_child(uint64_t index, const std::shared_ptr<Stmt> &stmt) {
    if (index < stmts_.size()) stmts_[index] = stmt;
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

ScopedStmtBlock & SwitchStmt::add_switch_case(const std::shared_ptr<Const> &switch_case,
                                 const std::shared_ptr<Stmt> &stmt) {
    stmt->set_parent(this);
    if (body_.find(switch_case) == body_.end()) {
        body_.emplace(switch_case, std::make_shared<ScopedStmtBlock>());
    }
    if (stmt->type() == StatementType::Block) {
        // merge the block
        auto blk = stmt->as<StmtBlock>();
        for (auto const &s: *blk) {
            body_[switch_case]->add_stmt(s);
        }
    } else {
        body_[switch_case]->add_stmt(stmt);
    }
    return *body_[switch_case];
}

ScopedStmtBlock & SwitchStmt::add_switch_case(const std::shared_ptr<Const> &switch_case,
                                 const std::vector<std::shared_ptr<Stmt>> &stmts) {
    for (auto &stmt : stmts) add_switch_case(switch_case, stmt);
    return *body_[switch_case];
}

void SwitchStmt::remove_switch_case(const std::shared_ptr<kratos::Const> &switch_case) {
    if (body_.find(switch_case) != body_.end()) {
        body_.erase(switch_case);
    }
}

void SwitchStmt::remove_switch_case(const std::shared_ptr<kratos::Const> &switch_case,
                                    const std::shared_ptr<kratos::Stmt> &stmt) {
    if (body_.find(switch_case) != body_.end()) {
        auto &stmts = body_.at(switch_case);
        stmts->remove_stmt(stmt);
    }
}

void SwitchStmt::remove_stmt(const std::shared_ptr<kratos::Stmt> &stmt) {
    for (auto &[c, stmts]: body_) {
        for (auto const &s: *stmts) {
            if (s == stmt) {
                remove_switch_case(c, stmt);
                break;
            }
        }
    }
}

IRNode *SwitchStmt::get_child(uint64_t index) {
    if (index == 0) {
        return target_.get();
    } else {
        index--;
        for (auto const &iter : body_) {
            if (index-- == 0) return iter.second.get();
        }
        return nullptr;
    }
}

std::unordered_set<std::shared_ptr<AssignStmt>> filter_assignments_with_target(
    const std::unordered_set<std::shared_ptr<AssignStmt>> &stmts, const Generator *target,
    bool lhs) {
    std::unordered_set<std::shared_ptr<AssignStmt>> result;
    for (const auto &stmt : stmts) {
        if (lhs) {
            if (stmt->left()->generator == target) result.emplace(stmt);
        } else {
            if (stmt->right()->generator == target) result.emplace(stmt);
        }
    }
    return result;
}

std::map<std::pair<uint32_t, uint32_t>, std::shared_ptr<VarSlice>> filter_slice_pairs_with_target(
    const std::map<std::pair<uint32_t, uint32_t>, std::shared_ptr<VarSlice>> &slices,
    Generator *target, bool lhs) {
    std::map<std::pair<uint32_t, uint32_t>, std::shared_ptr<VarSlice>> result;
    for (auto const &[slice_pair, slice] : slices) {
        if (!filter_assignments_with_target(slice->sources(), target, lhs).empty()) {
            result.emplace(slice_pair, slice);
        }
    }
    return result;
}

ModuleInstantiationStmt::ModuleInstantiationStmt(Generator *target, Generator *parent)
    : Stmt(StatementType::ModuleInstantiation), target_(target), parent_(parent) {
    auto const &port_names = target->get_port_names();
    for (auto const &port_name : port_names) {
        auto const &port = target->get_port(port_name);
        auto const port_direction = port->port_direction();
        if (port_direction == PortDirection::In) {
            // if we're connected to a base variable and no slice, we are good
            const auto &slices = filter_slice_pairs_with_target(port->get_slices(), parent, false);
            const auto &sources = filter_assignments_with_target(port->sources(), parent, false);
            // because an input cannot be an register, it can only has one
            // source (all bits combined)
            if (slices.empty()) {
                if (sources.empty())
                    throw ::runtime_error(
                        ::format("{0}.{1} is not connected", target->name, port_name));
                if (sources.size() > 1)
                    throw ::runtime_error(
                        ::format("{0}.{1} is driven by multiple nets", target->name, port_name));
                // add it to the port mapping and we are good to go
                auto const &stmt = *sources.begin();
                port_mapping_.emplace(port, stmt->right());
                if (parent->debug) {
                    port_debug_.emplace(port, stmt);
                }
            } else {
                // you need to run a de-slice pass on the module references first
                throw ::runtime_error(
                    "Input slices not supported in the statement. "
                    "Please run a de-couple pass first");
            }
        } else if (port_direction == PortDirection::Out) {
            // need to find out if there is any sources connected to the slices
            const auto &slices = filter_slice_pairs_with_target(port->get_slices(), parent, true);
            const auto &sinks = filter_assignments_with_target(port->sinks(), parent, true);
            if (slices.empty()) {
                if (!sinks.empty() && sinks.size() == 1) {
                    auto stmt = *sinks.begin();
                    port_mapping_.emplace(port, stmt->left());
                    if (parent->debug) {
                        port_debug_.emplace(port, stmt);
                    }
                } else if (!sinks.empty() && sinks.size() > 1) {
                    throw ::runtime_error(
                        "Output slices not supported in the statement. "
                        "Please run a de-couple pass first");
                }
            }
        } else {
            throw ::runtime_error("Inout port type not implemented");
        }
    }
}

}