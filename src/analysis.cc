#include "analysis.hh"

#include <iostream>
#include <mutex>

#include "codegen.hh"
#include "except.hh"
#include "fmt/format.h"
#include "graph.hh"
#include "interface.hh"
#include "stmt.hh"
#include "syntax.hh"
#include "util.hh"

using fmt::format;
using std::runtime_error;

namespace kratos {
class VerifyAssignmentVisitor : public IRVisitor {
public:
    void visit(AssignStmt* stmt) override {
        auto* const left = stmt->left();
        auto* right = stmt->right();
        // if the right hand side is a const and it's safe to do so, we will let it happen
        if (left->width() != right->width()) {
            if (right->type() == VarType::ConstValue) {
                auto old_value = right->as<Const>();
                try {
                    auto& new_const =
                        constant(old_value->value(), left->width(), old_value->is_signed());
                    stmt->set_right(new_const.shared_from_this());
                    right = &new_const;
                } catch (::runtime_error&) {
                    std::cerr << "Failed to convert constants. Expect an exception" << std::endl;
                }
            }
        }
        if (left->width() != right->width())
            throw StmtException(
                ::format("assignment width doesn't match. left ({0}): {1} right ({2}): {3}",
                         left->to_string(), left->width(), right->to_string(), right->width()),
                {stmt, left, right, left->width_param(), right->width_param()});
        if (left->is_signed() != right->is_signed())
            throw StmtException(
                ::format("assignment sign doesn't match. left ({0}): {1} right ({2}): {3}",
                         left->to_string(), left->is_signed(), right->to_string(),
                         right->is_signed()),
                {stmt, left, right, left->width_param(), right->width_param()});
        check_expr(right, stmt);
    }

    void visit(Generator* generator) override {
        auto vars = generator->get_all_var_names();
        for (auto const& var_name : vars) {
            auto var = generator->get_var(var_name);
            check_var(var.get());
        }
    }

private:
    void inline static check_var(Var* var) {
        bool is_top_level = false;
        auto const& sources = var->sources();
        for (auto const& stmt : sources) {
            if (stmt->parent()->ir_node_kind() == IRNodeKind::GeneratorKind) {
                is_top_level = true;
                break;
            }
        }

        // second pass the check all the assignments
        bool has_error = false;
        if (is_top_level) {
            for (auto const& stmt : sources) {
                if (stmt->parent()->ir_node_kind() != IRNodeKind::GeneratorKind) {
                    has_error = true;
                    break;
                }
            }
        }

        if (has_error) {
            std::vector<Stmt*> stmt_list;
            stmt_list.reserve(sources.size());
            // prepare the error
            for (auto const& stmt : sources) {
                stmt_list.emplace_back(stmt.get());
            }
            throw StmtException(::format("{0} has wire assignment yet is also used in always block",
                                         var->to_string()),
                                stmt_list.begin(), stmt_list.end());
        }
    }

    void static inline check_expr(Var* var, Stmt* stmt) {
        if (var->type() == VarType::Expression) {
            auto* expr = reinterpret_cast<Expr*>(var);
            auto* left = expr->left;
            auto* right = expr->right;
            auto width = var->width();
            bool is_relational = is_relational_op(expr->op);
            bool is_reduction = is_reduction_op(expr->op);
            bool is_expand = is_expand_op(expr->op);
            if (!is_relational && !is_reduction && left->width() != width && !is_expand) {
                throw VarException(::format("{0}'s width should be {1} but used as {2}",
                                            left->to_string(), left->width(), width),
                                   {var, left, stmt, left->width_param()});
            }
            if (!is_relational && !is_reduction && right && right->width() != width && !is_expand) {
                throw VarException(::format("{0}'s width should be {1} but used as {2}",
                                            right->to_string(), right->width(), width),
                                   {var, right, stmt, right->width_param()});
            }
            if (left->type() == VarType::Expression) {
                check_expr(left, stmt);
            }
            if (right && right->type() == VarType::Expression) {
                check_expr(right, stmt);
            }
        }
    }
};

void verify_assignments(Generator* top) {
    // verify the assignment width match, and sign as well
    VerifyAssignmentVisitor visitor;
    visitor.visit_root_s(top);
}

class MixedAssignmentVisitor : public IRVisitor {
public:
    void visit(Generator* generator) override {
        auto const vars = generator->get_vars();
        auto const ports = generator->get_port_names();
        for (const auto& var_name : vars) {
            checkout_assignment(generator, var_name);
        }
        for (const auto& port_name : ports) {
            checkout_assignment(generator, port_name);
        }
    }

private:
    static void checkout_assignment(Generator* generator, const std::string& name) {
        auto const& var = generator->get_var(name);
        AssignmentType type = AssignmentType::Undefined;
        for (auto const& stmt : var->sources()) {
            if (stmt->left()->get_var_root_parent() != var.get()) continue;
            if (type == AssignmentType ::Undefined)
                type = stmt->assign_type();
            else if (type != stmt->assign_type()) {
                std::vector<Stmt*> stmt_list;
                stmt_list.reserve(var->sources().size());
                for (const auto& st : var->sources()) stmt_list.emplace_back(st.get());
                throw StmtException(::format("Mixed assignment detected for variable {0}.{1}",
                                             generator->name, name),
                                    stmt_list.begin(), stmt_list.end());
            }
            // check assignment
            check_var_parent(generator, stmt->left(), stmt->right(), stmt.get());
        }
    }

    static bool has_non_port(Generator* context, Var* var) {
        if (!var) return false;
        if (var->type() == VarType::Expression) {
            auto* expr = dynamic_cast<Expr*>(var);
            return has_non_port(context, expr->left) || has_non_port(context, expr->right);
        } else if (var->type() == VarType::Slice) {
            auto* slice = dynamic_cast<VarSlice*>(var);
            return has_non_port(context, slice->parent_var);
        } else {
            return var->generator() != context && var->type() != VarType::PortIO &&
                   var->type() != VarType ::ConstValue;
        }
    }

    static void check_var_parent(Generator* generator, Var* dst_var, Var* var, Stmt* stmt) {
        auto* gen = var->generator();
        if (gen == Const::const_gen()) return;
        if (var->type() == VarType::ConstValue && var->generator() != generator) {
            var->set_generator(gen);
            return;
        }
        if (generator != gen) {
            // if it's an input port, the parent context is different
            if (dst_var->type() == VarType::Slice) {
                auto* slice = dynamic_cast<VarSlice*>(dst_var);
                dst_var = const_cast<Var*>(slice->get_var_root_parent());
            }
            if (dst_var->type() == VarType::PortIO) {
                auto* port = dynamic_cast<Port*>(dst_var);
                if (port->port_direction() == PortDirection::In) {
                    auto* context_g = dst_var->generator()->parent();
                    if (gen != context_g && gen->parent() != context_g &&
                        gen->parent() != context_g) {
                        throw VarException(
                            ::format("{0}.{1} cannot be wired to {2}.{3} because {0} is "
                                     "not a child generator of {2}",
                                     generator->instance_name, dst_var->to_string(),
                                     gen->instance_name, var->to_string()),
                            {generator, gen, dst_var, var});
                    }
                    return;
                }
            }
            if ((gen->parent() != generator && gen->parent() != generator->parent()) ||
                has_non_port(generator, var)) {
                throw VarException(::format("{0}.{1} cannot be wired to {2}.{3} because {2} is "
                                            "not a child generator of {0}",
                                            generator->instance_name, dst_var->to_string(),
                                            gen->instance_name, var->to_string()),
                                   {generator, gen, dst_var, var, stmt});
            }
        }
    }
};

void check_mixed_assignment(Generator* top) {
    MixedAssignmentVisitor visitor;
    visitor.visit_generator_root_tp(top);
}

class SynthesizableVisitor : public IRVisitor {
public:
    void visit(AssignStmt* stmt) override {
        if (stmt->has_delay()) {
            nodes_.emplace_back(stmt);
        }
    }

    void visit(FunctionCallVar* var) override {
        auto* const def = var->func();
        if (def->is_dpi() || def->is_task()) {
            nodes_.emplace_back(var);
        }
    }

    void visit(FunctionCallStmt* stmt) override {
        auto const& def = stmt->func();
        if (def->is_dpi()) {
            nodes_.emplace_back(stmt);
        } else if (def->is_builtin()) {
            auto info = get_builtin_function_info(def->function_name());
            if (info && !info->synthesizable) {
                nodes_.emplace_back(stmt);
            }
        }
    }

    void visit(AuxiliaryStmt* stmt) override { nodes_.emplace_back(stmt); }

    void visit(InitialStmtBlock* stmt) override { nodes_.emplace_back(stmt); }

    void visit(CombinationalStmtBlock* stmt) override {
        if (stmt->is_general_purpose()) nodes_.emplace_back(stmt);
    }

    const std::vector<IRNode*>& nodes() const { return nodes_; }

private:
    std::vector<IRNode*> nodes_;
};

void check_non_synthesizable_content(Generator* top) {
    SynthesizableVisitor visitor;
    visitor.visit_root(top);
    auto const& nodes = visitor.nodes();
    if (!nodes.empty()) {
        print_nodes(nodes);
        throw UserException(
            "Non-synthesizable content detected. Please see the relevant lines "
            "output above (after using debug mode)");
    }
}

class ActiveVisitor : public IRVisitor {
    // we can be very clever about how to detect the wrong negative
    // 1. we determine the activate low or high from the sequential conditions
    // 2. whenever we meet a if reset statement, we check it against it
    //    because if the async reset is used properly, we will determine the port type first first
    //    if the port is used as an sync reset, the port active type will be undefined.
public:
    void visit(IfStmt* stmt) override {
        auto predicate = stmt->predicate();
        // notice this just catch some simple mistakes
        // thus is designed to be zero false negative
        if (predicate->type() == VarType::PortIO) {
            auto port_s = predicate->as<Port>();
            auto* port = port_s.get();
            if (port->port_type() == PortType::AsyncReset) {
                if (reset_map_.find(port) == reset_map_.end()) {
                    // it's used as a sync reset
                    throw VarException(
                        ::format("{0} is used has a synchronous reset", port->to_string()),
                        {port, stmt});
                }
                bool reset_high = reset_map_.at(port);
                if (!reset_high)
                    throw VarException("Active low signal used as active high", {port, stmt});
            } else if (port->port_type() == PortType::Reset) {
                if (reset_map_.find(port) != reset_map_.end()) {
                    throw VarException(::format("{0} is synchronous reset but used as async reset",
                                                port->to_string()),
                                       {port, stmt, get_reset_stmt(port)});
                }
            }
        } else if (predicate->type() == VarType::Expression) {
            auto expr = predicate->as<Expr>();
            if (expr->op == ExprOp::UNot || expr->op == ExprOp::UInvert) {
                auto var = expr->left->as<Var>();
                if (var->type() == VarType::PortIO) {
                    auto port = var->as<Port>();
                    if (port->port_type() == PortType::AsyncReset) {
                        if (reset_map_.find(port.get()) == reset_map_.end()) {
                            // it's used as a sync reset
                            throw VarException(
                                ::format("{0} is used has a synchronous reset", port->to_string()),
                                {port.get(), stmt});
                        }
                        bool reset_high = reset_map_.at(port.get());
                        if (reset_high) {
                            throw VarException("Active high signal used as active low",
                                               {port.get(), stmt});
                        }
                    } else if (port->port_type() == PortType::Reset) {
                        if (reset_map_.find(port.get()) != reset_map_.end()) {
                            throw VarException(
                                ::format("{0} is synchronous reset but used as async reset",
                                         port->to_string()),
                                {port.get(), stmt, get_reset_stmt(port.get())});
                        }
                    }
                }
            }
        }
    }

    void visit(SequentialStmtBlock* stmt) override {
        auto const& sensitivity = stmt->get_event_controls();
        for (auto const& event : sensitivity) {
            auto t = event.edge;
            auto* v = event.var;
            if (v->type() == VarType::PortIO) {
                auto port_s = v->as<Port>();
                auto* port = port_s.get();
                if (port->port_type() == PortType::AsyncReset) {
                    auto reset_high = t == EventEdgeType::Posedge;
                    // check if we have reset edge set
                    if (port->active_high()) {
                        if (reset_high != (*port->active_high())) {
                            throw VarException(
                                ::format("{0} is declared reset {1} but is used as reset {2}",
                                         port->to_string(), reset_high ? "low" : "high",
                                         reset_high ? "high" : "low"),
                                {port, stmt});
                        }
                    }
                    if (reset_map_.find(port) != reset_map_.end()) {
                        // check consistency
                        if (reset_map_.at(port) != reset_high) {
                            throw VarException(
                                ::format("Inconsistent active low/high usage for {0}",
                                         port->to_string()),
                                {port, stmt, get_reset_stmt(port)});
                        }
                    } else {
                        reset_map_.emplace(std::make_pair(port, reset_high));
                        reset_map_.emplace(std::make_pair(port, stmt));
                    }
                } else if (port->port_type() == PortType::Reset) {
                    throw VarException(
                        ::format("{0} is used as async reset but is declared synchronous",
                                 port->to_string()),
                        {port, stmt});
                }
            }
        }
    }

private:
    std::unordered_map<Port*, bool> reset_map_;
    std::unordered_map<Port*, Stmt*> reset_stmt_;

    Stmt* get_reset_stmt(Port* port) const {
        if (reset_stmt_.find(port) != reset_stmt_.end()) return reset_stmt_.at(port);
        return nullptr;
    }
};

void check_active_high(Generator* top) {
    ActiveVisitor visitor;
    visitor.visit_root_s(top);
}

bool check_stmt_condition(Stmt* stmt, const std::function<bool(Stmt*)>& cond,
                          bool check_unreachable = false, bool full_branch = true) {
    if (cond(stmt)) {
        return true;
    } else if (stmt->type() == StatementType::Block) {
        // it has to be the last block
        uint64_t index;
        bool found = false;
        auto* block = dynamic_cast<StmtBlock*>(stmt);
        if (!block)
            throw InternalException("Statement is not block but is marked as StatementType::Block");
        auto stmt_count = block->size();
        for (index = 0; index < stmt_count; index++) {
            auto* s = block->get_stmt(index).get();
            if (check_stmt_condition(s, cond, check_unreachable, full_branch)) {
                found = true;
                break;
            }
        }
        if (found && check_unreachable) {
            if (index != block->size() - 1) {
                // we have unreachable state
                std::vector<Stmt*> stmts;
                for (uint64_t i = index + 1; i < block->size(); i++)
                    stmts.emplace_back(block->get_stmt(i).get());
                throw StmtException("Unreachable code block", stmts.begin(), stmts.end());
            }
        }
        return found;
    } else if (stmt->type() == StatementType::Switch) {
        auto* stmt_ = dynamic_cast<SwitchStmt*>(stmt);
        if (!stmt_)
            throw InternalException(
                "Statement is not switch but is marked as StatementType::Switch");
        auto cases = stmt_->body();
        if (cases.empty()) return false;
        uint32_t found_case = 0;
        for (auto const& iter : cases) {
            auto* scope_stmt = iter.second.get();
            if (check_stmt_condition(scope_stmt, cond, check_unreachable, full_branch))
                found_case++;
            else if (full_branch)
                return false;
        }
        // make sure default case is covered
        // if there is no default case, all the cases have to be covered
        // the only exception is that if the target is an enum and we've covered all it's enum case
        uint32_t targeted_cases;
        if (stmt_->target()->is_enum()) {
            auto* enum_var = dynamic_cast<EnumType*>(stmt_->target().get());
            if (!enum_var) throw InternalException("Unable to resolve enum type");
            auto const* enum_def = enum_var->enum_type();
            targeted_cases = enum_def->values.size();
        } else {
            targeted_cases = 1u << stmt_->target()->width();
        }
        if (full_branch) {
            return cases.find(nullptr) != cases.end() || found_case == targeted_cases;
        } else {
            return found_case > 0;
        }
    } else if (stmt->type() == StatementType::If) {
        auto* stmt_ = dynamic_cast<IfStmt*>(stmt);
        if (!stmt_)
            throw InternalException("Statement is not if but is marked as StatementType::If");
        auto const& then = stmt_->then_body();
        auto const& else_ = stmt_->else_body();
        if (full_branch) {
            return check_stmt_condition(then.get(), cond, check_unreachable, full_branch) &&
                   check_stmt_condition(else_.get(), cond, check_unreachable, full_branch);
        } else {
            return check_stmt_condition(then.get(), cond, check_unreachable, full_branch) ||
                   check_stmt_condition(else_.get(), cond, check_unreachable, full_branch);
        }
    } else if (stmt->type() == StatementType::For) {
        auto* stmt_ = dynamic_cast<ForStmt*>(stmt);
        if (!stmt_)
            throw InternalException("Statement is not if but is marked as StatementType::For");
        auto body = stmt_->get_loop_body();
        return check_stmt_condition(body.get(), cond, check_unreachable, full_branch);
    }
    return false;
}

class FunctionReturnVisitor : public IRVisitor {
public:
    void visit(Generator* generator) override {
        // check all the function definitions
        auto functions = generator->functions();
        for (auto const& iter : functions) {
            auto func = iter.second;
            // check if the function has a return
            if (!func->has_return_value() || func->is_builtin()) continue;
            // build statement graph
            bool has_return = check_stmt_condition(
                func.get(),
                [](Stmt* stmt) -> bool { return stmt->type() == StatementType::Return; }, true);
            if (!has_return) {
                std::vector<Stmt*> stmts;
                stmts.reserve(func->size());
                for (uint64_t i = 0; i < func->size(); i++) {
                    stmts.emplace_back(func->get_stmt(i).get());
                }
                throw StmtException(
                    ::format("{0} does not have return statement in all control flows",
                             func->function_name()),
                    stmts.begin(), stmts.end());
            }
        }
    }
};

void check_function_return(Generator* top) {
    FunctionReturnVisitor visitor;
    visitor.visit_generator_root_p(top);
}

class LatchVisitor : public IRVisitor {
public:
    void visit(Generator* generator) override {
        uint64_t stmt_count = generator->stmts_count();
        for (uint64_t i = 0; i < stmt_count; i++) {
            auto stmt = generator->get_stmt(i);
            if (stmt->type() == StatementType::Block) {
                auto blk = stmt->as<StmtBlock>();
                if (blk->block_type() == StatementBlockType::Combinational) {
                    // multiple passes to extract assigned variables
                    auto stmt_ = blk->as<CombinationalStmtBlock>();
                    check_combinational(stmt_.get());
                } else if (blk->block_type() == StatementBlockType::Sequential) {
                    // multiple passes to extract assigned variables
                    auto stmt_ = blk->as<SequentialStmtBlock>();
                    check_sequential(stmt_.get());
                }
            }
        }
    }

private:
    bool static check_stmt_block(StmtBlock* stmt, Var* var, bool full_branch) {
        return check_stmt_condition(
            stmt,
            [=](Stmt* s) -> bool {
                if (s->type() == StatementType::Assign) {
                    auto assign = s->as<AssignStmt>();
                    return assign->left() == var;
                }
                return false;
            },
            false, full_branch);
    }

    static void check_stmt_block(StmtBlock* stmt, Var* var, const std::vector<Stmt*>& stmts,
                                 bool full_branch) {
        auto check = [=](Stmt* s) -> bool {
            if (s->type() == StatementType::Assign) {
                auto* assign = reinterpret_cast<AssignStmt*>(s);
                auto* left = assign->left();
                if (left->type() == VarType::Slice) {
                    auto* slice = reinterpret_cast<VarSlice*>(left);
                    left = const_cast<Var*>(slice->get_var_root_parent());
                }
                return left == var;
            } else if (s->type() == StatementType::Block) {
                auto* block = reinterpret_cast<StmtBlock*>(s);
                if (block->block_type() == StatementBlockType::Function) {
                    // function call to set the variable
                    return check_stmt_block(block, var, full_branch);
                }
            }
            return false;
        };
        if (!check_stmt_condition(stmt, check, false, full_branch)) {
            // things goes wrong
            // need to recover all the statements
            throw StmtException(::format("{0} will be inferred as latch", var->to_string()),
                                stmts.begin(), stmts.end());
        }
    }

    void static check_combinational(CombinationalStmtBlock* stmt) {
        AssignedVarVisitor visitor;
        visitor.visit_root(stmt);
        const auto& vars = visitor.assigned_vars();
        for (auto const& iter : vars) {
            check_stmt_block(stmt, iter.first, iter.second, true);
        }
    }

    void static check_sequential(SequentialStmtBlock* stmt) {
        auto const& conditions = stmt->get_event_controls();
        // we care about non-clock
        for (auto const& iter : conditions) {
            auto* var = iter.var;
            if (var->type() == VarType::PortIO) {
                auto* port = reinterpret_cast<Port*>(var);
                if (port->port_type() == PortType::Clock) continue;
            }
            // check every if statement that's targeted by that variable
            IfVisitor visitor(var);
            visitor.visit_root(stmt);
            auto ifs = visitor.ifs();
            // derive the variables to check
            for (auto const& if_ : ifs) {
                AssignedVarVisitor a_v;
                a_v.visit_root(if_->then_body().get());
                auto vars = a_v.assigned_vars();
                for (auto const& [v, stmts] : vars) {
                    check_stmt_block(if_->else_body().get(), v, stmts, false);
                }
            }
        }
    }

    class IfVisitor : public IRVisitor {
    public:
        explicit IfVisitor(Var* var) : var_(var) {}
        void visit(IfStmt* stmt) override {
            if (has_var(stmt->predicate().get(), var_)) ifs_.emplace(stmt);
        }
        const std::unordered_set<IfStmt*>& ifs() const { return ifs_; }

    private:
        Var* var_;
        std::unordered_set<IfStmt*> ifs_;

        bool static has_var(Var* var, Var* target) {
            if (var->type() == VarType::Expression) {
                auto* expr = var->as<Expr>().get();
                bool left = has_var(expr->left, target);
                bool right = expr->right ? has_var(expr->right, target) : false;
                return left || right;
            } else {
                if (var->type() == VarType::Slice) {
                    auto* slice = reinterpret_cast<VarSlice*>(var);
                    var = const_cast<Var*>(slice->get_var_root_parent());
                }
                return var == target;
            }
        }
    };

    class AssignedVarVisitor : public IRVisitor {
    public:
        void visit(AssignStmt* stmt) override {
            auto* left = stmt->left();
            if (left->type() == VarType::Slice) {
                auto* slice = reinterpret_cast<VarSlice*>(left);
                if (slice->sliced_by_var()) {
                    return;
                }
                left = const_cast<Var*>(slice->get_var_root_parent());
            }
            assigned_vars_[left].emplace_back(stmt);
        }
        const std::unordered_map<Var*, std::vector<Stmt*>>& assigned_vars() const {
            return assigned_vars_;
        }

    private:
        std::unordered_map<Var*, std::vector<Stmt*>> assigned_vars_;
    };
};

void check_inferred_latch(Generator* top) {
    LatchVisitor visitor;
    visitor.visit_generator_root_p(top);
}

class MultipleDriverVisitor : public IRVisitor {
public:
    void visit(Generator* gen) override {
        auto var_names = gen->get_vars();
        for (auto const& name : var_names) {
            auto const& var = gen->get_var(name);
            check_var(var.get());
        }

        auto port_names = gen->get_port_names();
        for (auto const& name : port_names) {
            auto const& port = gen->get_port(name);
            check_var(port.get());
        }
    }

private:
    static bool share_root(IRNode* node1, IRNode* node2) {
        std::set<IRNode*> nodes1;
        std::set<IRNode*> nodes2;
        while (node1->parent() && node1->parent()->ir_node_kind() == IRNodeKind::StmtKind) {
            nodes1.emplace(node1);
            node1 = node1->parent();
        }
        while (node2->parent() && node2->parent()->ir_node_kind() == IRNodeKind::StmtKind) {
            nodes2.emplace(node2);
            node2 = node2->parent();
        }
        std::set<IRNode*> diff;
        std::set_intersection(nodes1.begin(), nodes1.end(), nodes2.begin(), nodes2.end(),
                              std::inserter(diff, diff.begin()));
        return !diff.empty();
    }

    static bool has_for_loop(Stmt* stmt) {
        if (stmt->type() == StatementType::For) {
            return true;
        } else {
            auto* p = stmt->parent();
            if (p && p->ir_node_kind() == IRNodeKind::StmtKind) {
                return has_for_loop(reinterpret_cast<Stmt*>(p));
            }
        }
        return false;
    }

    static void check_var(Var* var) {
        std::unordered_map<uint32_t, std::pair<IRNode*, Stmt*>> parents;
        for (auto const& stmt : var->sources()) {
            // TODO: FIX THIS
            //  This is a hack to bypass the check if there is a for loop
            if (has_for_loop(stmt.get())) continue;
            auto* v = stmt->left();
            if (v->get_var_root_parent() != var) continue;
            if (v->type() == VarType::Slice) {
                auto slice = v->as<VarSlice>();
                if (slice->sliced_by_var()) continue;
            }
            uint32_t var_low = v->var_low();
            uint32_t var_high = v->var_high();
            for (uint32_t i = var_low; i <= var_high; i++) {
                if (parents.find(i) != parents.end()) {
                    auto* parent = stmt->parent();
                    auto* stmt_parent = non_gen_root_parent(stmt.get());
                    auto const& [ref_parent, ref_stmt_parent] = parents.at(i);
                    // the purpose of the following statement is to make sure that there is no
                    // other assignment that's assigning the same var slice in the same scope
                    // it cannot be driven through different blocks, either.
                    // notice that there is a caveat. in combinational block, as long as the
                    // they are in the same stmt parent, they can have different scope, since
                    // having different scope implies priority. as a result, we need to filter
                    // this case out
                    bool has_multiple_driver = stmt_parent != ref_stmt_parent;
                    if (!has_multiple_driver) {
                        // skip the special case
                        if (parent == ref_parent) {
                            has_multiple_driver = true;
                            if (stmt_parent->ir_node_kind() == IRNodeKind::StmtKind) {
                                auto* st = dynamic_cast<Stmt*>(stmt_parent);
                                if (st && st->type() == StatementType::Block) {
                                    auto* block = dynamic_cast<StmtBlock*>(st);
                                    if (block->block_type() == StatementBlockType::Combinational ||
                                        block->block_type() == StatementBlockType::Latch) {
                                        has_multiple_driver = false;
                                    }
                                }
                            }
                        } else {
                            if (stmt_parent->ir_node_kind() == IRNodeKind::StmtKind) {
                                auto* st = dynamic_cast<Stmt*>(stmt_parent);
                                if (st && st->type() == StatementType::Block) {
                                    auto* block = dynamic_cast<StmtBlock*>(st);
                                    if (block->block_type() == StatementBlockType::Sequential) {
                                        // TODO: this algorithm is not perfect as it only
                                        //  accounts for standalone assignments
                                        has_multiple_driver = !share_root(parent, ref_parent);
                                    }
                                }
                            }
                        }
                    }
                    if (has_multiple_driver) {
                        throw StmtException(::format("{0} has multiple driver in the same scope",
                                                     var->handle_name()),
                                            {var, parent, stmt.get()});
                    }
                } else {
                    parents.emplace(
                        i, std::make_pair(stmt->parent(), non_gen_root_parent(stmt.get())));
                }
            }
        }
    }

    static Stmt* non_gen_root_parent(Stmt* stmt) {
        // this is just to get the root stmt parent that's holding given stmt
        IRNode* parent = stmt;
        uint32_t count = 0;
        while (parent->parent() && parent->parent()->ir_node_kind() == IRNodeKind::StmtKind) {
            parent = parent->parent();
            // this is to prevent infinite loop
            if (count++ > 10000) {
                throw InternalException(::format("Unable to find parent for statement"));
            }
        }
        return reinterpret_cast<Stmt*>(parent);
    }
};

void check_multiple_driver(Generator* top) {
    MultipleDriverVisitor visitor;
    visitor.visit_generator_root_tp(top);
}

class CombinationalLoopVisitor : public IRVisitor {
public:
    void visit(Generator* gen) override {
        auto var_names = gen->get_vars();
        for (auto const& name : var_names) {
            auto const& var = gen->get_var(name);
            check_var(var.get());
        }

        auto port_names = gen->get_port_names();
        for (auto const& name : port_names) {
            auto const& port = gen->get_port(name);
            check_var(port.get());
        }
    }

private:
    static void check_var(Var* var) {
        // get all the sources
        auto const& sources = var->sources();
        for (auto const& stmt : sources) {
            if (stmt->assign_type() == AssignmentType::Blocking && has_var(stmt->right(), var) &&
                stmt->parent()->ir_node_kind() == IRNodeKind::GeneratorKind) {
                throw StmtException(::format("Combinational loop detected at {0} <- {1}",
                                             stmt->left()->to_string(), stmt->right()->to_string()),
                                    {stmt.get(), var});
            }
        }
    }

    static bool has_var(Var* var, Var* target) {
        if (!var) return false;
        if (var == target) return true;
        if (var->type() == VarType::Expression) {
            auto* expr = reinterpret_cast<Expr*>(var);
            return has_var(expr->left, target) || has_var(expr->right, target);
        }
        return false;
    }
};

void check_combinational_loop(Generator* top) {
    CombinationalLoopVisitor visitor;
    visitor.visit_generator_root_tp(top);
}

class CheckFlipFlopAlwaysFFVisitor : public IRVisitor {
public:
    void visit(Generator* gen) override {
        uint64_t stmt_count = gen->stmts_count();
        for (uint64_t i = 0; i < stmt_count; i++) {
            auto stmt = gen->get_stmt(i);
            if (stmt->type() == StatementType::Block) {
                auto block = stmt->as<StmtBlock>();
                if (block->block_type() == StatementBlockType::Sequential) {
                    check_always_ff(block->as<SequentialStmtBlock>().get());
                }
            }
        }
    }

private:
    void static check_always_ff(SequentialStmtBlock* stmt) {
        // first pass to determine if there is any if statement in top level
        bool has_if = false;
        uint64_t i = 0;
        uint64_t stmt_count = stmt->size();
        while ((!has_if) && (i < stmt_count)) {
            auto s = stmt->get_stmt(i);
            if (s->type() == StatementType::If) has_if = true;
            i++;
        }
        if (has_if && stmt->size() > 1) {
            // DC cannot infer as a D-flip-flop
            // error message copied from DC
            throw StmtException(
                "The statements in this 'always' block are outside the "
                "scope of the synthesis policy. Only an ’if’ statement "
                "is allowed at the top level in this ’always’ block. (ELAB-302)",
                {stmt});
        }
    }
};

void check_flip_flop_always_ff(Generator* top) {
    CheckFlipFlopAlwaysFFVisitor visitor;
    visitor.visit_generator_root_p(top);
}

class EnableStmtVisitor : public IRVisitor {
public:
    void visit(AssignStmt* stmt) override {
        // we're only interested in top level blocking assignment
        if (stmt->assign_type() != AssignmentType::Blocking) return;
        auto* left = stmt->left();
        auto str_value = get_ssa_enable_condition(left);
        if (!str_value.empty()) {
            values.emplace(stmt, str_value);
        }
    }

    void visit(ScopedStmtBlock* stmt) override {
        auto count = stmt->size();
        auto* gen = stmt->generator_parent();
        for (auto i = 0u; i < count; i++) {
            auto const& s = stmt->get_stmt(i);
            auto cond = get_cond(s.get());
            if (cond) {
                values.emplace(s.get(), cond->handle_name(gen));
            }
        }
    }

    std::unordered_map<const Stmt*, std::string> values;

private:
    static std::shared_ptr<Var> get_cond(Stmt* stmt) {
        auto* ir_parent = stmt->parent();
        if (ir_parent->ir_node_kind() == IRNodeKind::GeneratorKind) {
            return nullptr;
        }
        auto* parent_stmt = reinterpret_cast<Stmt*>(ir_parent);
        std::shared_ptr<Var> expr;
        if (parent_stmt->type() == StatementType::If) {
            // need to figure out which block it belongs to
            auto* if_ = reinterpret_cast<IfStmt*>(parent_stmt);
            if (if_->then_body().get() == stmt) {
                expr = if_->predicate();
            } else {
                expr = if_->predicate()->r_not().shared_from_this();
            }
        } else if (parent_stmt->type() == StatementType::Switch) {
            auto* switch_ = reinterpret_cast<SwitchStmt*>(parent_stmt);
            // figure out which condition it is in. notice that we could be in the default
            // branch as well
            auto const& body = switch_->body();
            bool found = false;
            for (auto const& [cond, stmt_blk] : body) {
                if (stmt_blk.get() == stmt) {
                    // it's this condition
                    if (cond) expr = switch_->target()->eq(*cond).shared_from_this();
                    found = true;
                    break;
                }
            }
            if (!found) {
                throw StmtException("Incorrect statement block stage", {stmt});
            }
            if (!expr) {
                // it's the default one. we nor them together
                std::shared_ptr<Var> or_;
                std::vector<std::shared_ptr<Const>> conditions;
                conditions.reserve(body.size());
                for (auto const& [cond, stmt_blk] : body) {
                    if (cond) conditions.emplace_back(cond);
                }
                // sort conditions based on the value. it's guarantee to be unique
                // so no problems of overlap
                std::sort(
                    conditions.begin(), conditions.end(),
                    [](const std::shared_ptr<Const>& left, const std::shared_ptr<Const>& right) {
                        return left->value() < right->value();
                    });
                or_ = conditions[0];
                if (conditions.size() > 1) {
                    for (uint64_t i = 1; i < conditions.size(); i++) {
                        or_ = or_->operator||(*conditions[i]).shared_from_this();
                    }
                }
                expr = (switch_->target()->operator!=(*or_)).shared_from_this();
            }
        } else {
            return get_cond(parent_stmt);
        }
        auto rest_expr = get_cond(parent_stmt);
        if (rest_expr) {
            return expr->operator&&(*rest_expr).shared_from_this();
        } else {
            return expr;
        }
    }

    static std::string get_ssa_enable_condition(Var* target) {
        std::vector<std::string> str_values;
        // check attributes
        auto const& attrs = target->get_attributes();
        if (!attrs.empty()) {
            for (auto const& attr : attrs) {
                auto val = get_ssa_en(attr.get());
                if (val) str_values.emplace_back(*val);
            }
        }

        return string::join(str_values.begin(), str_values.end(), " and ");
    }

    static std::optional<std::string> get_ssa_en(const Attribute* attr) {
        auto const& value_str = attr->value_str;
        constexpr auto en_str = "ssa-en=";
        auto static const start_pos = std::string(en_str).size();
        auto pos = value_str.rfind(en_str);
        if (pos == 0) {
            auto v = value_str.substr(start_pos);
            return v;
        } else {
            return std::nullopt;
        }
    }
};

std::unordered_map<const Stmt*, std::string> compute_enable_condition(Generator* top) {
    // notice that this pass assumes SSA pass has transformed the always_comb block into
    // top-level continuous assignment
    EnableStmtVisitor visitor;
    visitor.visit_root(top);
    return visitor.values;
}

class PortPackedVisitor : public IRVisitor {
public:
    void visit(Generator* generator) override {
        auto const& var_names = generator->get_all_var_names();
        for (auto const& var_name : var_names) {
            auto var = generator->get_var(var_name);
            if (var->is_struct()) {
                std::shared_ptr<PackedStruct> struct_def;
                if (var->type() == VarType::PortIO) {
                    auto ptr = var->as<PortPackedStruct>();
                    struct_def = ptr->packed_struct();
                } else {
                    auto ptr = var->as<VarPackedStruct>();
                    struct_def = ptr->packed_struct();
                }
                if (struct_def->external) continue;
                process_struct_(struct_def.get(), var.get());
            }
        }
    }

    [[nodiscard]] std::vector<const PackedStruct*> structs() const {
        PackedStructGraph g;
        for (auto const& [_, s] : structs_) {
            add_struct(&g, nullptr, s);
        }

        return g.get_structs();
    }

private:
    std::map<std::string, const PackedStruct*> structs_;
    std::map<std::string, Var*> struct_ports_;

    void process_struct_(PackedStruct* struct_def, Var* var) {
        if (structs_.find(struct_def->struct_name) != structs_.end()) {
            // do some checking
            auto const* struct_ = structs_.at(struct_def->struct_name);
            if (!struct_def->same(*struct_)) {
                throw VarException(::format("redefinition of different packed struct {0}",
                                            struct_def->struct_name),
                                   {var, struct_ports_.at(struct_def->struct_name)});
            }
        } else {
            structs_.emplace(struct_def->struct_name, struct_def);
            struct_ports_.emplace(struct_def->struct_name, var);

            // check if there is any struct inside attributes
            for (auto const& attr : struct_def->attributes) {
                if (attr.struct_) {
                    process_struct_(attr.struct_, var);
                }
            }
        }
    }

    static void add_struct(PackedStructGraph* g, const PackedStruct* s,
                           const PackedStruct* parent) {
        auto* parent_node = g->get_node(parent);
        auto* n = g->get_node(s);
        if (n) {
            n->parent = parent_node;
            parent_node->children.emplace(n);
        }

        // look for child definition
        for (auto const& attr : parent->attributes) {
            if (attr.struct_) {
                add_struct(g, parent, attr.struct_);
            }
        }
    }
};

std::map<std::string, std::string> extract_struct_info(Generator* top) {
    PortPackedVisitor visitor;
    visitor.visit_generator_root(top);

    // convert the definition into
    std::map<std::string, std::string> result;
    auto const structs = visitor.structs();
    for (uint32_t i = 0; i < structs.size(); i++) {
        auto const* struct_ = structs[i];
        // TODO:
        //  Use Stream class in the codegen instead to track the debugging info
        //  Share the same code gen logic with Stream
        std::string entry;
        entry.append("typedef struct packed {\n");

        for (auto const& def : struct_->attributes) {
            if (!def.struct_) {
                std::vector<std::string> str = {"    logic"};
                if (def.width > 1) str.emplace_back(::format("[{0}:0]", def.width - 1));
                if (def.signed_) str.emplace_back("signed");
                str.emplace_back(def.name);
                auto entry_str = string::join(str.begin(), str.end(), " ");
                entry.append(entry_str + ";\n");
            } else {
                entry.append(def.struct_->struct_name + " " + def.name + ";\n");
            }
        }
        entry.append(::format("}} {0};\n", struct_->struct_name));
        // this is a hack to ensure ordering. refactoring this requires refactoring
        // code from the caller site
        auto name = fmt::format("{0:032d}", i);
        result.emplace(name, entry);
    }
    return result;
}

class DPIVisitor : public IRVisitor {
public:
    void visit(FunctionStmtBlock* stmt) override {
        if (!stmt->is_dpi()) return;
        // collect all the dpi information and then make sure they are declared in the same
        // name and spec
        // this can be an issue if the files are going to split into multiple files
        auto const& func_name = stmt->function_name();
        if (dpi_funcs_.find(func_name) == dpi_funcs_.end()) {
            // new one
            dpi_funcs_.emplace(func_name, dynamic_cast<DPIFunctionStmtBlock*>(stmt));
        } else {
            auto* ref_stmt = dpi_funcs_.at(func_name);
            auto const& ref_ports = ref_stmt->ports();
            auto const& ports = stmt->ports();
            if (ref_ports.size() != ports.size())
                throw StmtException("DPI function " + func_name + " has different interface",
                                    {stmt, ref_stmt});
            // check the return width
            auto* dpi_stmt = dynamic_cast<DPIFunctionStmtBlock*>(stmt);
            if (dpi_stmt->return_width() != ref_stmt->return_width()) {
                if (ref_ports.size() != ports.size())
                    throw StmtException("DPI function " + func_name + " has different interface",
                                        {stmt, ref_stmt});
            }
            for (auto const& [port_name, port_ref] : ref_ports) {
                if (ports.find(port_name) == ports.end()) {
                    throw VarException(
                        ::format("DPI function with the same name ({0}) have different interface",
                                 func_name),
                        {port_ref.get()});
                }
                auto const& port = ports.at(port_name);
                if (port->size() != port_ref->size() ||
                    port->is_signed() != port_ref->is_signed() ||
                    port->port_direction() != port_ref->port_direction()) {
                    throw VarException(
                        ::format("DPI function with the same name ({0}) have different interface",
                                 func_name),
                        {port_ref.get(), port.get()});
                }
            }
            if (dpi_stmt->is_context() != ref_stmt->is_context() ||
                dpi_stmt->is_pure() != ref_stmt->is_pure())
                throw StmtException(
                    "DPI function " + func_name + " has different attribute (pure/context)",
                    {stmt, ref_stmt});
        }
    }

    const std::map<std::string, DPIFunctionStmtBlock*>& dpi_funcs() { return dpi_funcs_; }

private:
    std::map<std::string, DPIFunctionStmtBlock*> dpi_funcs_;
};

std::map<std::string, std::string> extract_dpi_function(Generator* top, bool int_interface) {
    DPIVisitor visitor;
    visitor.visit_root(top);
    // code gen these dpi info
    std::map<std::string, std::string> result;
    auto const& dpi_funcs = visitor.dpi_funcs();
    for (auto const& [func_name, stmt] : dpi_funcs) {
        std::stringstream stream;
        // dpi-c
        std::string dpi_type;
        if (stmt->is_pure())
            dpi_type = " pure";
        else if (stmt->is_context())
            dpi_type = " context";
        stream << "import \"DPI-C\"" << dpi_type << " function ";
        // based on the return width, we choose the closest one
        if (stmt->return_width() == 0) {
            stream << "void ";
        } else if (stmt->return_width() == 1) {
            stream << "bit ";
        } else if (stmt->return_width() <= 8) {
            stream << "byte ";
        } else if (stmt->return_width() <= 16) {
            stream << "shortint ";
        } else if (stmt->return_width() <= 32) {
            stream << "int ";
        } else {
            stream << "longint ";
        }
        stream << stmt->function_name() << "(";
        auto ports = stmt->ports();
        std::vector<std::string> port_str;
        port_str.reserve(ports.size());
        std::vector<std::string> port_names;
        port_names.reserve(ports.size());
        for (auto const& iter : ports) port_names.emplace_back(iter.first);

        // sort based on ordering
        auto const& ordering = stmt->port_ordering();
        std::sort(port_names.begin(), port_names.end(), [&](const auto& lhs, const auto& rhs) {
            return ordering.at(lhs) < ordering.at(rhs);
        });

        for (auto const& port_name : port_names) {
            if (int_interface) {
                auto port = ports.at(port_name);
                // compute the closest width
                std::string type_str;
                if (port->width() <= 8) {
                    type_str = "byte";
                } else if (port->width() <= 16) {
                    type_str = "shortint";
                } else if (port->width() <= 32) {
                    type_str = "int";
                } else {
                    type_str = "longint";
                }
                std::vector<std::string> strs{
                    port->port_direction() == PortDirection::In ? "input" : "output", type_str};
                if (port->is_signed()) strs.emplace_back("signed");
                strs.emplace_back(port_name);
                port_str.emplace_back(string::join(strs.begin(), strs.end(), " "));
            } else {
                port_str.emplace_back(
                    SystemVerilogCodeGen::get_port_str(ports.at(port_name).get()));
            }
        }
        stream << string::join(port_str.begin(), port_str.end(), ", ");
        stream << ");";

        result.emplace(func_name, stream.str());
    }
    return result;
}

std::map<std::string, std::string> extract_enum_info(Generator* top) {
    auto const& enum_defs = top->context()->enum_defs();

    std::map<std::string, std::string> result;
    for (auto const& [enum_name, def] : enum_defs) {
        if (def->external) continue;
        auto str = SystemVerilogCodeGen::enum_code(def.get());
        result.emplace(enum_name, str);
    }

    return result;
}

class InterfaceVisitor : public IRVisitor {
public:
    void visit(Generator* generator) override {
        // local variables
        uint64_t stmt_count = generator->stmts_count();
        for (uint64_t i = 0; i < stmt_count; i++) {
            auto stmt = generator->get_stmt(i);
            if (stmt->type() == StatementType::InterfaceInstantiation) {
                visit(stmt->as<InterfaceInstantiationStmt>().get());
            }
        }
        // ports as well
        std::set<const InterfaceRef*> refs;
        for (auto const& port_name : generator->get_port_names()) {
            auto p = generator->get_port(port_name);
            if (p->is_interface()) {
                auto interface_p = p->as<InterfacePort>();
                const auto* ref = interface_p->interface();
                auto def = ref->definition();
                update_interface_definition(def, ref, generator);
            }
        }
    }

    void visit(InterfaceInstantiationStmt* stmt) override {
        auto def = stmt->interface()->definition();
        update_interface_definition(def, stmt->interface(), stmt->generator_parent());
    }

    const std::unordered_map<std::string, std::pair<Generator*, const InterfaceRef*>>& interfaces()
        const {
        return interfaces_;
    }

private:
    std::unordered_map<std::string, std::pair<Generator*, const InterfaceRef*>> interfaces_;
    std::mutex lock_;

    void update_interface_definition(const std::shared_ptr<IDefinition>& def,
                                     const InterfaceRef* ref, Generator* gen) {
        lock_.lock();
        if (interfaces_.find(def->def_name()) == interfaces_.end()) {
            interfaces_.emplace(def->def_name(), std::make_pair(gen, ref));
            lock_.unlock();
        } else {
            // making sure they are the same
            auto const& [reg_gen, ref_interface] = interfaces_.at(def->def_name());
            auto ref_def = ref_interface->definition();
            lock_.unlock();
            auto const& ports = def->ports();
            if (ref_def->ports() != ports)
                throw UserException(::format("{0}.{1}'s interface differs from {2}.{3}'s",
                                             gen->handle_name(), def->def_name(),
                                             reg_gen->handle_name(), ref_def->def_name()));
            for (auto const& port_name : ports) {
                if (def->port(port_name) != ref_def->port(port_name))
                    throw UserException(::format("{0}.{1}'s interface differs from {2}.{3}'s",
                                                 gen->handle_name(), def->def_name(),
                                                 reg_gen->handle_name(), ref_def->def_name()));
            }
            // same var as well
            auto const& vars = def->vars();
            if (ref_def->vars() != vars)
                throw UserException(::format("{0}.{1}'s interface differs from {2}.{3}'s",
                                             gen->handle_name(), def->def_name(),
                                             reg_gen->handle_name(), ref_def->def_name()));
            for (auto const& port_name : vars) {
                if (def->var(port_name) != ref_def->var(port_name))
                    throw UserException(::format("{0}.{1}'s interface differs from {2}.{3}'s",
                                                 gen->handle_name(), def->def_name(),
                                                 reg_gen->handle_name(), ref_def->def_name()));
            }
        }
    }
};

std::map<std::string, std::string> extract_interface_info(Generator* top) {
    InterfaceVisitor visitor;
    visitor.visit_generator_root_p(top);
    auto const& defs = visitor.interfaces();
    std::map<std::string, std::string> result;
    const std::string indent = "  ";
    for (auto const& [interface_name, def] : defs) {
        const auto* i_ref = def.second;
        auto const& i_def = i_ref->definition();
        if (i_def->is_modport())
            // don't generate mod port definition
            continue;
        std::stringstream stream;
        stream << "interface " << interface_name;
        if (!i_def->ports().empty()) {
            stream << "(" << std::endl;
            auto port_names = i_def->ports();
            uint32_t i = 0;
            for (auto const& port_name : port_names) {
                auto* p = &i_ref->port(port_name);
                stream << indent << SystemVerilogCodeGen::get_port_str(p);
                if (i++ == port_names.size() - 1)
                    stream << std::endl;
                else
                    stream << "," << std::endl;
            }
            stream << ");" << std::endl;
        } else {
            stream << ";" << std::endl;
        }
        // output vars
        auto const& vars = i_def->vars();
        for (auto const& var_name : vars) {
            auto* v = &i_ref->var(var_name);
            stream << indent << Stream::get_var_decl(v) << ";" << std::endl;
        }

        // modports
        auto interface_definition = std::static_pointer_cast<InterfaceDefinition>(i_def);
        auto const& mod_ports = interface_definition->mod_ports();
        for (auto const& [mod_name, mod_port] : mod_ports) {
            stream << indent << "modport " << mod_name << "(";
            auto const& ports = mod_port->ports();
            if (ports.empty()) throw UserException(::format("{0} is empty", mod_name));
            auto const& inputs = mod_port->inputs();
            auto const& outputs = mod_port->outputs();
            uint32_t count = 0;
            for (auto const& name : inputs) {
                stream << "input " << name;
                if (++count != ports.size()) stream << ", ";
            }
            for (auto const& name : outputs) {
                stream << "output " << name;
                if (++count != ports.size()) stream << ", ";
            }
            stream << ");" << std::endl;
        }
        stream << "endinterface" << std::endl;
        result.emplace(interface_name, stream.str());
    }
    return result;
}

class GeneratorVarVisitor : public IRVisitor {
public:
    explicit GeneratorVarVisitor(bool registers_only) : registers_only_(registers_only) {}

    void visit(Generator* generator) override {
        auto vars = generator->get_all_var_names();
        for (auto const& var_name : vars) {
            auto const& var = generator->get_var(var_name);
            if (!var)
                throw InternalException(
                    ::format("Cannot get {0} from {1}", var_name, generator->name));
            // detect if it has any non-blocking assignment
            auto const& sources = var->sources();
            if (registers_only_) {
                if (sources.empty()) continue;
                auto const& stmt = *(sources.begin());
                // only if a variable has non-blocking assignment
                // we assume that at this state we have already have all the assignment checked and
                // fixed
                if (stmt->assign_type() == AssignmentType::NonBlocking)
                    names_.emplace_back(var->handle_name());
            } else {
                names_.emplace_back(var->handle_name());
            }
        }
    }

    const std::vector<std::string>& names() const { return names_; }

private:
    bool registers_only_;
    std::vector<std::string> names_;
};

std::vector<std::string> extract_register_names(Generator* top) {
    // first fix the assignment types
    fix_assignment_type(top);
    // this pass extract the absolute handle name for each generator accessible from the top
    // no need for parallel version since the pass is so simple, otherwise we have to use mutex
    // lock on names
    GeneratorVarVisitor visitor(true);
    visitor.visit_generator_root(top);
    return visitor.names();
}

std::vector<std::string> extract_var_names(Generator* top) {
    GeneratorVarVisitor visitor(false);
    visitor.visit_generator_root(top);
    return visitor.names();
}

class SensitivityVisitor : public IRVisitor {
    void visit(SequentialStmtBlock* stmt) override {
        auto const& sensitivity_list = stmt->get_event_controls();
        for (auto const& iter : sensitivity_list) {
            auto* var = iter.var;
            // check type
            if (var->type() == VarType::PortIO) {
                // it's a port
                auto port = var->as<Port>();
                if (port->port_type() != PortType::Clock &&
                    port->port_type() != PortType::AsyncReset) {
                    // only clock and async reset allowed
                    throw StmtException(
                        ::format("Only Clock and AsyncReset allowed in "
                                 "sensitivity list. {0} is {1}",
                                 var->to_string(), port_type_to_str(port->port_type())),
                        {stmt, var});
                }
            } else if (var->type() == VarType::BaseCasted) {
                auto var_casted = var->as<VarCasted>();
                if (var_casted->cast_type() != VarCastType::Clock &&
                    var_casted->cast_type() != VarCastType::AsyncReset) {
                    throw StmtException(::format("Only Clock and AsyncReset allowed in "
                                                 "sensitivity list. Please use cast() to cast {0}}",
                                                 var->to_string()),
                                        {stmt, var});
                }
            } else {
                throw StmtException(::format("Only variable type of Clock and "
                                             "AsyncReset allowed in sensitivity list, got {0}",
                                             var->to_string()),
                                    {stmt, var});
            }
        }
    }
};

void check_always_sensitivity(Generator* top) {
    SensitivityVisitor visitor;
    visitor.visit_root(top);
}

bool connected(const std::shared_ptr<Port>& port, std::unordered_set<uint32_t>& bits) {
    bool result = false;
    bits.reserve(port->width());
    if (!port->sources().empty()) {
        // it has been assigned. need to compute all the slices
        auto sources = port->sources();
        for (const auto& stmt : sources) {
            auto* src = stmt->left();
            if (src->type() == VarType::Slice) {
                auto ptr = src->as<VarSlice>();
                auto* ptr_parent = ptr->get_var_root_parent();
                uint32_t high, low;
                if (ptr_parent != port.get()) {
                    // it got be a sliced by var
                    if (!ptr->sliced_by_var())
                        throw VarException("Internal error. Variable has un-related sources",
                                           {port.get()});
                    // it's actually not driven by the current net
                    continue;
                } else {
                    if (ptr->sliced_by_var()) {
                        // possibly to hit all bits
                        low = 0;
                        high = port->width() - 1;
                    } else {
                        low = ptr->var_low();
                        high = ptr->var_high();
                    }
                }
                for (uint32_t i = low; i <= high; i++) {
                    bits.emplace(i);
                }
            } else {
                result = true;
                for (uint32_t i = 0; i < port->width(); i++) bits.emplace(i);
                break;
            }
        }
    }
    if (result && bits.size() != port->width()) result = false;
    return result;
}

class GeneratorConnectivityVisitor : public IRVisitor {
public:
    GeneratorConnectivityVisitor() = default;

    void visit(Generator* generator) override {
        // skip if it's an external module or stub module
        if (generator->external() || generator->is_stub()) return;
        const auto& port_names = generator->get_port_names();
        for (const auto& port_name : port_names) {
            auto const& port = generator->get_port(port_name);

            // based on whether it's an input or output
            // for inputs, if it's not top generator, we need to check if
            // something is driving it
            if (port->port_direction() == PortDirection::In) {
                if (is_top_level_) continue;
            }

            std::unordered_set<uint32_t> bits;
            bool has_error = !connected(port, bits);

            if (has_error) {
                std::vector<Stmt*> stmt_list;
                for (auto const& stmt : port->sources()) {
                    stmt_list.emplace_back(stmt.get());
                }
                for (uint32_t i = 0; i < port->width(); i++) {
                    if (bits.find(i) == bits.end()) {
                        throw StmtException(
                            ::format("{0}[{1}] is a floating net. Please check your connections",
                                     port->handle_name(), i),
                            stmt_list.begin(), stmt_list.end());
                    }
                }
            }
        }

        is_top_level_ = false;
    }

private:
    bool is_top_level_ = true;
};

void verify_generator_connectivity(Generator* top) {
    GeneratorConnectivityVisitor visitor;
    visitor.visit_generator_root(top);
}

}  // namespace kratos