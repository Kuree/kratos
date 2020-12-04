#include "stmt.hh"

#include <algorithm>
#include <cassert>

#include "except.hh"
#include "fmt/format.h"
#include "generator.hh"
#include "interface.hh"
#include "port.hh"
#include "util.hh"

using fmt::format;
using std::move;

namespace kratos {

IRNode *Stmt::parent() { return parent_; }

Generator *Stmt::generator_parent() const {
    IRNode *p = parent_;
    // we don't do while loop here to prevent infinite loop
    // 100000 is sufficient for almost all designs.
    for (uint32_t i = 0; i < 100000u && p; i++) {
        if (p->ir_node_kind() != IRNodeKind::GeneratorKind) {
            p = p->parent();
        } else {
            break;
        }
    }
    if (!p || p->ir_node_kind() != IRNodeKind::GeneratorKind) {
        // special case for nested for loop
        if (type() == StatementType::Block && parent_ &&
            parent_->ir_node_kind() == IRNodeKind::StmtKind &&
            reinterpret_cast<Stmt *>(parent_)->type() == StatementType::For) {
            // take the best shot
            auto *for_ = reinterpret_cast<ForStmt *>(parent_);
            return for_->get_iter_var()->generator();
        }
        return nullptr;
    }
    return dynamic_cast<Generator *>(p);
}

void Stmt::set_scope_context(const std::map<std::string, std::pair<bool, std::string>> &context) {
    scope_context_ = context;
}

void Stmt::add_scope_variable(const std::string &name, const std::string &value, bool is_var,
                              bool override) {
    if (override || scope_context_.find(name) == scope_context_.end()) {
        scope_context_.emplace(name, std::make_pair(is_var, value));
    }
}

void Stmt::remove_from_parent() {
    if (!parent_) return;
    if (parent_->ir_node_kind() == IRNodeKind::GeneratorKind) {
        auto *gen = reinterpret_cast<Generator *>(parent_);
        gen->remove_stmt(shared_from_this());
    } else if (parent_->ir_node_kind() == IRNodeKind::StmtKind) {
        auto *stmt = reinterpret_cast<Stmt *>(parent_);
        stmt->remove_stmt(shared_from_this());
    } else {
        throw StmtException("Statement parent is null", {this});
    }
}

std::shared_ptr<Stmt> Stmt::clone() const {
    return std::const_pointer_cast<Stmt>(shared_from_this());
}

void Stmt::copy_meta(const std::shared_ptr<Stmt> &stmt) const {
    stmt->verilog_ln = verilog_ln;
    stmt->comment = comment;
}

AssignStmt::AssignStmt(const std::shared_ptr<Var> &left, const std::shared_ptr<Var> &right)
    : AssignStmt(left, right, AssignmentType::Undefined) {}

AssignStmt::AssignStmt(const std::shared_ptr<Var> &left, std::shared_ptr<Var> right,
                       AssignmentType type)
    : Stmt(StatementType ::Assign), left_(left.get()), right_(right.get()), assign_type_(type) {
    if (left == nullptr) throw UserException("left hand side is empty");
    if (right == nullptr) throw UserException("right hand side is empty");
    // check for sign
    if (left->is_signed() != right->is_signed()) {
        throw VarException(
            ::format("left ({0})'s sign does not match with right ({1}). {2} <- {3}",
                     left->to_string(), right->to_string(), left->is_signed(), right->is_signed()),
            {left.get(), right.get()});
    }
    // check for width
    if (left->width() != right->width()) {
        // up scale or down scale if the right hand side is a const, and it is allowed
        bool has_error = true;
        if (right->type() == VarType::ConstValue) {
            auto const_ = right->as<Const>();
            if (Const::is_legal(const_->value(), left->width(), left->is_signed()) ==
                Const::ConstantLegal::Legal) {
                has_error = false;
                const_->set_width(left->width());
            }
        } else if (IterVar::has_iter_var(right.get())) {
            // need to resize it
            if (IterVar::safe_to_resize(right.get(), left->width(), left->is_signed())) {
                // fix the width
                auto *right_ptr = right.get();
                IterVar::fix_width(right_ptr, left->width());
                right = right_ptr->shared_from_this();
                has_error = false;
            }
        }
        if (has_error || left->width() != right->width()) {
            throw VarException(
                ::format("left ({0})'s width does not match with right ({1}). {2} <- {3}",
                         left->to_string(), right->to_string(), left->width(), right->width()),
                {left.get(), right.get()});
        } else {
            // reassign
            right_ = right.get();
        }
    }
    if (((left->size().front() > 1 || left->size().size() > 1 || left->explicit_array()) ||
         (right->size().front() > 1 || right->size().size() > 1 || right->explicit_array())) &&
        left->is_packed() != right->is_packed()) {
        if (left->is_packed())
            throw StmtException(::format("left ({0}) is packed array but right ({1}) is not.",
                                         left->to_string(), right->to_string()),
                                {left.get(), right.get()});
        else
            throw StmtException(::format("right ({1}) is packed array but left ({0}) is not.",
                                         left->to_string(), right->to_string()),
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
        return left_;
    else if (index == 1)
        return right_;
    else
        return nullptr;
}

void AssignStmt::set_parent(kratos::IRNode *parent) {
    bool has_parent = parent_ != nullptr;
    Stmt::set_parent(parent);
    // push the stmt into its sources
    if (!has_parent) {
        // if it has parent, it means we've already added the source and sink
        right_->add_sink(as<AssignStmt>());
        if (parent) left_->add_source(as<AssignStmt>());
    }
}
std::shared_ptr<Stmt> AssignStmt::clone() const {
    auto stmt = std::make_shared<AssignStmt>(left_->shared_from_this(), right_->shared_from_this(),
                                             assign_type_);
    copy_meta(stmt);
    return stmt;
}

void AssignStmt::clear() {
    // remove it from source and sinks
    left_->remove_source(shared_from_this()->as<AssignStmt>());
    right_->remove_sink(shared_from_this()->as<AssignStmt>());
    parent_ = nullptr;
}

IfStmt::IfStmt(std::shared_ptr<Var> predicate)
    : Stmt(StatementType::If), predicate_(::move(predicate)) {
    then_body_ = std::make_shared<ScopedStmtBlock>();
    else_body_ = std::make_shared<ScopedStmtBlock>();

    then_body_->set_parent(this);
    else_body_->set_parent(this);

    // just to add the sinks
    predicate_stmt_ =
        predicate_->generator()->get_auxiliary_var(predicate_->width())->assign(predicate_);
    predicate_stmt_->set_parent(nullptr);
}

void IfStmt::set_predicate(const std::shared_ptr<Var> &var) {
    predicate_stmt_->clear();
    assert(var->ir_node_kind() == IRNodeKind::VarKind);
    predicate_ = var;
    predicate_stmt_ =
        predicate_->generator()->get_auxiliary_var(predicate_->width())->assign(predicate_);
    predicate_stmt_->set_parent(nullptr);
}

void IfStmt::add_then_stmt(const std::shared_ptr<Stmt> &stmt) {
    if (stmt->type() == StatementType::Block)
        throw StmtException("cannot add statement block to the if statement body", {this});
    then_body_->add_stmt(stmt);
}

void IfStmt::add_else_stmt(const std::shared_ptr<Stmt> &stmt) {
    if (stmt->type() == StatementType::Block)
        throw StmtException("cannot add statement block to the if statement body", {this});
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
    for (auto const &s : *else_body_) {
        if (s == stmt) {
            remove_else_stmt(stmt);
            return;
        }
    }
}

void IfStmt::set_then(const std::shared_ptr<ScopedStmtBlock> &stmt) {
    then_body_->clear();
    for (auto &s : *stmt) {
        then_body_->add_stmt(s);
    }
}

void IfStmt::set_else(const std::shared_ptr<ScopedStmtBlock> &stmt) {
    else_body_->clear();
    for (auto &s : *stmt) {
        else_body_->add_stmt(s);
    }
}

void IfStmt::set_parent(IRNode *node) {
    Stmt::set_parent(node);
    then_body_->set_parent(this);
    else_body_->set_parent(this);
    predicate_stmt_->set_parent(nullptr);
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

void IfStmt::add_scope_variable(const std::string &name, const std::string &value, bool is_var,
                                bool override) {
    Stmt::add_scope_variable(name, value, is_var, override);
    then_body_->add_scope_variable(name, value, is_var, override);
    else_body_->add_scope_variable(name, value, is_var, override);
}

std::shared_ptr<Stmt> IfStmt::clone() const {
    auto if_ = std::make_shared<IfStmt>(predicate_);
    auto then_clone = then_body_->clone();
    auto else_clone = else_body_->clone();

    if_->then_body_ = then_clone->as<ScopedStmtBlock>();
    if_->then_body_->set_parent(if_.get());
    if_->else_body_ = else_clone->as<ScopedStmtBlock>();
    if_->else_body_->set_parent(if_.get());

    copy_meta(if_);

    return if_;
}

void IfStmt::clear() {
    predicate_stmt_->clear();
    then_body_->clear();
    else_body_->clear();
}

ForStmt::ForStmt(const std::string &iter_var_name, int64_t start, int64_t end, int64_t step)
    : Stmt(StatementType::For), start_(start), end_(end), step_(step) {
    // making a loop variable
    // first determine if it is signed or not
    bool sign = start < 0 || end < 0;
    // the iter var used for iteration assignment
    iter_ = std::make_shared<IterVar>(nullptr, iter_var_name, start, end, sign);
    loop_body_ = std::make_shared<ScopedStmtBlock>();
    loop_body_->set_parent(this);
}

void ForStmt::set_parent(IRNode *node) {
    if (node->ir_node_kind() != IRNodeKind::StmtKind)
        throw UserException("For loop can only be added to statement body");
    auto *stmt = reinterpret_cast<Stmt *>(node);
    auto *gen = stmt->generator_parent();
    if (gen) {
        iter_->set_generator(gen);
    }
    Stmt::set_parent(node);
    for (auto &st : (*loop_body_)) {
        st->set_parent(this);
    }
}

IRNode *ForStmt::get_child(uint64_t index) { return index < 1 ? loop_body_.get() : nullptr; }

void ForStmt::add_stmt(const std::shared_ptr<Stmt> &stmt) { loop_body_->add_stmt(stmt); }

std::shared_ptr<Stmt> ForStmt::clone() const {
    auto stmt = std::make_shared<ForStmt>(iter_->name, start_, end_, step_);
    stmt->loop_body_ = loop_body_->clone()->as<ScopedStmtBlock>();
    stmt->loop_body_->set_parent(stmt.get());
    // share the iter expression
    stmt->iter_ = iter_;
    copy_meta(stmt);
    return stmt;
}

void ForStmt::clear() { loop_body_->clear(); }

StmtBlock::StmtBlock(StatementBlockType type) : Stmt(StatementType::Block), block_type_(type) {}

void StmtBlock::add_stmt(const std::shared_ptr<Stmt> &stmt) {
    if (!stmt) throw StmtException("Unable to add nullptr (None) to code block", {this});
    // it cannot add another block stmt
    if (stmt->type() == StatementType::Block) {
        throw StmtException("cannot add statement block to another statement block",
                            {this, stmt.get()});
    }
    if (std::find(stmts_.begin(), stmts_.end(), stmt) != stmts_.end()) {
        throw StmtException("Cannot add the same block to the block list", {this, stmt.get()});
    }
    // if it is an assign statement, check the assignment as well
    if (stmt->type() == StatementType::Assign) {
        auto assign_stmt = stmt->as<AssignStmt>();
        if (assign_stmt->assign_type() == AssignmentType::Undefined) {
            // let the passes to figure this out
        } else if (assign_stmt->assign_type() == AssignmentType::NonBlocking &&
                   block_type_ == StatementBlockType::Combinational) {
            throw StmtException("cannot add blocking assignment to a sequential block",
                                {this, stmt.get()});
        } else if (assign_stmt->assign_type() == AssignmentType::Blocking &&
                   block_type_ == StatementBlockType::Sequential) {
            throw StmtException("cannot add non-blocking assignment to a combinational block",
                                {this, stmt.get()});
        }
    }
    stmt->set_parent(this);
    stmts_.emplace_back(stmt);
}

void StmtBlock::clear() {
    for (auto &stmt : stmts_) {
        stmt->clear();
    }
    stmts_.clear();
}

void StmtBlock::set_parent(IRNode *parent) {
    Stmt::set_parent(parent);
    for (auto &stmt : stmts_) {
        stmt->set_parent(this);
    }
}

void StmtBlock::remove_stmt(const std::shared_ptr<kratos::Stmt> &stmt) {
    auto pos = std::find(stmts_.begin(), stmts_.end(), stmt);
    if (pos != stmts_.end()) stmts_.erase(pos);
}

void StmtBlock::set_child(uint64_t index, const std::shared_ptr<Stmt> &stmt) {
    if (index < stmts_.size()) {
        stmts_[index] = stmt;
        stmt->set_parent(this);
    }
}

void StmtBlock::add_scope_variable(const std::string &name, const std::string &value, bool is_var,
                                   bool override) {
    Stmt::add_scope_variable(name, value, is_var, override);
    for (auto &stmt : stmts_) {
        stmt->add_scope_variable(name, value, is_var, override);
    }
}

void StmtBlock::clone_block(kratos::StmtBlock *block) const {
    block->stmts_.clear();
    block->stmts_.reserve(stmts_.size());
    for (auto const &stmt : stmts_) {
        block->add_stmt(stmt->clone());
    }
    copy_meta(block->shared_from_this());
}

std::shared_ptr<Stmt> ScopedStmtBlock::clone() const {
    auto stmt = std::make_shared<ScopedStmtBlock>();
    clone_block(stmt.get());
    return stmt;
}

void SequentialStmtBlock::add_condition(
    const std::pair<BlockEdgeType, std::shared_ptr<Var>> &condition) {
    // notice that the condition variable cannot be used as a condition
    // for now we only allow Port (clk and reset) type to use as conditions
    // make sure no duplicate
    auto pos = std::find(conditions_.begin(), conditions_.end(), condition);
    if (pos != conditions_.end()) return;
    auto var = condition.second;
    conditions_.emplace_back(condition);
}

IRNode *SequentialStmtBlock::get_child(uint64_t index) {
    if (index < stmts_.size()) {
        return stmts_[index].get();
    } else if (index < stmts_.size() + conditions_.size()) {
        auto const &cond = conditions_[index - stmts_.size()];
        return cond.second.get();
    }
    return nullptr;
}

SwitchStmt::SwitchStmt(Var &target)
    : Stmt(StatementType::Switch), target_(target.shared_from_this()) {
    // we don't allow const target
    if (target.type() == VarType::ConstValue)
        throw StmtException(::format("switch target cannot be const value {0}", target.name),
                            {this, &target});

    // just to add the sinks
    target_stmt_ = target.generator()->get_auxiliary_var(target.width())->assign(target);
    target_stmt_->set_parent(nullptr);
}

void SwitchStmt::set_parent(IRNode *parent) {
    Stmt::set_parent(parent);
    for (auto &iter : body_) {
        iter.second->set_parent(this);
    }
}

ScopedStmtBlock &SwitchStmt::add_switch_case(const std::shared_ptr<Const> &switch_case,
                                             const std::shared_ptr<Stmt> &stmt) {
    stmt->set_parent(this);
    if (body_.find(switch_case) == body_.end()) {
        auto block = std::make_shared<ScopedStmtBlock>();
        block->set_parent(this);
        body_.emplace(switch_case, block);
    }
    if (stmt->type() == StatementType::Block) {
        // merge the block
        auto blk = stmt->as<StmtBlock>();
        for (auto const &s : *blk) {
            body_[switch_case]->add_stmt(s);
        }
    } else {
        body_[switch_case]->add_stmt(stmt);
    }
    return *body_[switch_case];
}

ScopedStmtBlock &SwitchStmt::add_switch_case(const std::shared_ptr<Const> &switch_case,
                                             const std::vector<std::shared_ptr<Stmt>> &stmts) {
    for (const auto &stmt : stmts) add_switch_case(switch_case, stmt);
    return *body_.at(switch_case);
}

ScopedStmtBlock &SwitchStmt::add_switch_case(Const &switch_case,
                                             const std::shared_ptr<Stmt> &stmt) {
    auto c = switch_case.as<Const>();
    return add_switch_case(c, stmt);
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
    for (auto &[c, stmts] : body_) {
        for (auto const &s : *stmts) {
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

void SwitchStmt::add_scope_variable(const std::string &name, const std::string &value, bool is_var,
                                    bool override) {
    Stmt::add_scope_variable(name, value, is_var, override);
    for (auto &iter : body_) {
        iter.second->add_scope_variable(name, value, is_var, override);
    }
}

std::shared_ptr<Stmt> SwitchStmt::clone() const {
    auto switch_ = std::make_shared<SwitchStmt>(target_);
    // clone the cases
    for (auto const &[cond, stmt] : body_) {
        auto cloned_stmt = stmt->clone()->as<ScopedStmtBlock>();
        cloned_stmt->set_parent(switch_.get());
        switch_->body_.emplace(cond, cloned_stmt);
    }

    copy_meta(switch_);
    return switch_;
}

void SwitchStmt::clear() {
    target_stmt_->clear();
    for (auto const &iter : body_) {
        iter.second->clear();
    }
}

std::shared_ptr<Stmt> CombinationalStmtBlock::clone() const {
    auto stmt = std::make_shared<CombinationalStmtBlock>();
    clone_block(stmt.get());
    return stmt;
}

std::shared_ptr<Stmt> SequentialStmtBlock::clone() const {
    auto stmt = std::make_shared<SequentialStmtBlock>();
    stmt->conditions_ = std::vector(conditions_);
    clone_block(stmt.get());
    return stmt;
}

std::shared_ptr<Stmt> LatchStmtBlock::clone() const {
    auto stmt = std::make_shared<LatchStmtBlock>();
    clone_block(stmt.get());
    return stmt;
}

std::unordered_set<std::shared_ptr<AssignStmt>> filter_assignments_with_target(
    const std::unordered_set<std::shared_ptr<AssignStmt>> &stmts, const Generator *target,
    bool lhs) {
    std::unordered_set<std::shared_ptr<AssignStmt>> result;
    for (const auto &stmt : stmts) {
        if (lhs) {
            if (stmt->left()->generator() == target) result.emplace(stmt);
        } else {
            if (stmt->right()->generator() == target) result.emplace(stmt);
        }
    }
    return result;
}

std::vector<std::shared_ptr<VarSlice>> filter_slice_pairs_with_target(
    const std::vector<std::shared_ptr<VarSlice>> &slices, Generator *target, bool lhs) {
    std::vector<std::shared_ptr<VarSlice>> result;
    result.reserve(slices.size());
    for (auto const &slice : slices) {
        if (!filter_assignments_with_target(slice->sources(), target, lhs).empty()) {
            result.emplace_back(slice);
        }
    }
    return result;
}

FunctionStmtBlock::FunctionStmtBlock(kratos::Generator *parent, std::string function_name)
    : StmtBlock(StatementBlockType::Function),
      parent_(parent),
      function_name_(std::move(function_name)) {}

void FunctionStmtBlock::create_function_handler(uint32_t width, bool is_signed) {
    if (function_handler_) {
        throw VarException(::format("{0} already has a function handler", function_name_),
                           {function_handler_.get()});
    }
    function_handler_ =
        std::make_shared<Port>(parent_, PortDirection::In, function_name_ + "_return", width, 1,
                               PortType::Data, is_signed);
}

std::shared_ptr<Port> FunctionStmtBlock::input(const std::string &name, uint32_t width,
                                               bool is_signed) {
    auto p = std::make_shared<Port>(parent_, PortDirection::In, name, width, 1, PortType::Data,
                                    is_signed);
    ports_.emplace(name, p);
    return p;
}

std::shared_ptr<Port> FunctionStmtBlock::get_port(const std::string &port_name) {
    if (ports_.find(port_name) == ports_.end())
        throw UserException(::format("cannot find {0}", port_name));
    return ports_.at(port_name);
}

std::shared_ptr<ReturnStmt> FunctionStmtBlock::return_stmt(const std::shared_ptr<Var> &var) {
    return std::make_shared<ReturnStmt>(this, var);
}

void FunctionStmtBlock::set_port_ordering(const std::map<std::string, uint32_t> &ordering) {
    if (ordering.size() != ports_.size())
        throw UserException("Port ordering size does not match with declared outputs");
    for (auto const &iter : ordering) {
        if (ports_.find(iter.first) == ports_.end())
            throw UserException(::format("{0} does not exist"));
    }
    port_ordering_ = ordering;
}

void FunctionStmtBlock::set_port_ordering(const std::map<uint32_t, std::string> &ordering) {
    std::map<std::string, uint32_t> result;
    for (auto const &[index, name] : ordering) {
        result.emplace(name, index);
    }
    set_port_ordering(result);
}

std::shared_ptr<Port> DPIFunctionStmtBlock::output(const std::string &name, uint32_t width,
                                                   bool is_signed) {
    // record the ordering
    port_ordering_.emplace(name, port_ordering_.size());
    auto p = std::make_shared<Port>(parent_, PortDirection::Out, name, width, 1, PortType::Data,
                                    is_signed);
    ports_.emplace(name, p);
    return p;
}

std::shared_ptr<Port> DPIFunctionStmtBlock::input(const std::string &name, uint32_t width,
                                                  bool is_signed) {
    // record the ordering
    port_ordering_.emplace(name, port_ordering_.size());
    return FunctionStmtBlock::input(name, width, is_signed);
}

void DPIFunctionStmtBlock::set_is_context(bool value) {
    is_context_ = value;
    is_pure_ = !value;
}

void DPIFunctionStmtBlock::set_is_pure(bool value) {
    is_pure_ = value;
    is_context_ = !value;
}

std::unordered_map<std::string, uint32_t> BuiltInFunctionStmtBlock::known_functions_;
BuiltInFunctionStmtBlock::BuiltInFunctionStmtBlock(Generator *parent,
                                                   const std::string &function_name)
    : FunctionStmtBlock(parent, function_name) {
    // check known functions
    if (known_functions_.empty()) {
        // initialize
        // all the known functions should be synthesizable
        known_functions_ = {{"clog2", 32}};
    }
    if (known_functions_.find(function_name) == known_functions_.end()) {
        std::string known_functions;
        for (auto const &iter : known_functions_) {
            known_functions += ::format("\n  {0}", iter.first);
        }
        throw UserException(
            ::format("{0} is either not supported or not a system. Supported methods are:{1}",
                     function_name, known_functions));
    }
}

ReturnStmt::ReturnStmt(FunctionStmtBlock *func_def, std::shared_ptr<Var> value)
    : Stmt(StatementType::Return), func_def_(func_def), value_(std::move(value)) {}

void ReturnStmt::set_parent(kratos::IRNode *parent) {
    Stmt::set_parent(parent);
    // looping to make sure there is a function statement block
    // it will never be 10k deep. this is to avoid infinite loop when construction failed
    /* comment this out because can only be determined after every statements has been set
     * TODO:
     * add a pass to analysis returns
    IRNode *ir_p = parent;
    bool found = false;
    FunctionStmtBlock *stmt = nullptr;
    for (uint32_t i = 0; i < 10000; i++) {
        if (!ir_p)
            break;
        auto ptr = dynamic_cast<FunctionStmtBlock *>(ir_p);
        if (ptr) {
            found = true;
            stmt = ptr;
            break;
        }
        ir_p = ir_p->parent();
    }

    if (!found) {
        throw ::runtime_error("Can only add return statement to function block");
    }
     */
    func_def_->set_has_return_value(true);
    // need to handle the assignments
    if (!func_def_->function_handler()) {
        // create a function handler
        func_def_->create_function_handler(value_->width(), value_->is_signed());
    }
    auto p = func_def_->function_handler();
    auto s = p->assign(value_, AssignmentType::Blocking);
    s->set_parent(this);
}

FunctionCallStmt::FunctionCallStmt(const std::shared_ptr<FunctionStmtBlock> &func,
                                   const std::map<std::string, std::shared_ptr<Var>> &args)
    : Stmt(StatementType::FunctionalCall), func_(func) {
    // check the function call types
    auto ports = func->ports();
    for (auto const &[port_name, func_port] : ports) {
        if (args.find(port_name) == args.end()) {
            throw VarException(::format("{0} is not connected", port_name), {func_port.get()});
        }
        // check the port types
        const auto &arg_port = args.at(port_name);
        if (func_port->width() != arg_port->width())
            throw VarException(::format("{0}'s width doesn't match", port_name),
                               {func_port.get(), arg_port.get()});
        if (func_port->is_signed() != arg_port->is_signed())
            throw VarException(::format("{0}'s sign doesn't match", port_name),
                               {func_port.get(), arg_port.get()});
    }
    auto *generator = func->generator();
    auto &p = generator->call(func->function_name(), args, false);
    var_ = p.as<FunctionCallVar>();
}

FunctionCallStmt::FunctionCallStmt(const std::shared_ptr<FunctionCallVar> &var)
    : Stmt(StatementType::FunctionalCall), func_(var->func()->as<FunctionStmtBlock>()), var_(var) {}

std::shared_ptr<Stmt> FunctionCallStmt::clone() const { throw UserException("Not implemented"); }

void InstantiationStmt::process_port(kratos::Port *port, Generator *parent,
                                     const std::string &target_name) {
    auto const port_direction = port->port_direction();
    auto const &port_name = port->name;
    if (port_direction == PortDirection::In) {
        // if we're connected to a base variable and no slice, we are good
        const auto &slices = filter_slice_pairs_with_target(port->get_slices(), parent, false);
        const auto &sources = filter_assignments_with_target(port->sources(), parent, false);
        // because an input cannot be an register, it can only has one
        // source (all bits combined)
        if (slices.empty()) {
            if (sources.empty())
                throw VarException(::format("{0}.{1} is not connected", target_name, port_name),
                                   {port});
            if (sources.size() > 1)
                throw VarException(
                    ::format("{0}.{1} is driven by multiple nets", target_name, port_name), {port});
            // add it to the port mapping and we are good to go
            auto const &stmt = *sources.begin();
            port_mapping_.emplace(port, stmt->right());
            if (parent->debug) {
                port_debug_.emplace(port, stmt.get());
            }
            // add it to the mapping list
            connection_stmt_.emplace(stmt.get());
            // remove it from the parent
            stmt->remove_from_parent();
        } else {
            // you need to run a de-slice pass on the module references first
            throw InternalException(
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
                stmt->remove_from_parent();
                if (parent->debug) {
                    port_debug_.emplace(port, stmt.get());
                }
            } else if (!sinks.empty() && sinks.size() > 1) {
                throw InternalException(
                    "Multiple outputs not supported in the statement. "
                    "Please run a de-couple pass first");
            }
        } else {
            throw InternalException(
                "Output slices not supported in the statement. "
                "Please run a de-couple pass first");
        }
    } else {
        throw InternalException("Inout port type not implemented");
    }
}

ModuleInstantiationStmt::ModuleInstantiationStmt(Generator *target, Generator *parent)
    : Stmt(StatementType::ModuleInstantiation), target_(target) {
    auto const &port_names = target->get_port_names();
    for (auto const &port_name : port_names) {
        auto const &port_shared = target->get_port(port_name);
        auto *port = port_shared.get();
        process_port(port, parent, target->name);
    }
    target->has_instantiated() = true;
}

InterfaceInstantiationStmt::InterfaceInstantiationStmt(kratos::Generator *parent,
                                                       kratos::InterfaceRef *interface)
    : Stmt(StatementType::InterfaceInstantiation), interface_(interface) {
    for (auto const &[port_name, port] : interface->ports()) {
        process_port(port, parent, interface->name());
    }
    interface->has_instantiated() = true;
}

CommentStmt::CommentStmt(std::string comment, uint32_t line_width) : Stmt(StatementType::Comment) {
    // erase the new line
    std::string::size_type pos = 0;
    while ((pos = comment.find('\n', pos)) != std::string::npos) {
        comment.erase(pos, 1);
    }
    comments_ = line_wrap(comment, line_width);
}

std::shared_ptr<Stmt> CommentStmt::clone() const {
    auto stmt = std::make_shared<CommentStmt>();
    stmt->comments_ = std::vector(comments_);
    copy_meta(stmt);
    return stmt;
}

RawStringStmt::RawStringStmt(const std::string &stmt) : Stmt(StatementType::RawString) {
    // split the raw based on the \r and \n
    auto lines = string::get_tokens(stmt, "\r\n");
    for (auto const &line : lines) {
        if (!line.empty()) {
            stmts_.emplace_back(line);
        }
    }
}

RawStringStmt::RawStringStmt(const std::vector<std::string> &stmt)
    : Stmt(StatementType::RawString) {
    for (auto const &lines : stmt) {
        auto tokens = string::get_tokens(lines, "\r\n");
        for (auto const &line : tokens) {
            if (!line.empty()) {
                stmts_.emplace_back(line);
            }
        }
    }
}

std::shared_ptr<Stmt> RawStringStmt::clone() const {
    auto stmt = std::make_shared<RawStringStmt>(stmts_);
    copy_meta(stmt);
    return stmt;
}

}  // namespace kratos
