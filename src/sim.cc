#include "sim.hh"
#include "eval.hh"
#include "except.hh"
#include "fmt/format.h"
#include "pass.hh"
#include "stmt.hh"
#include "util.hh"

using fmt::format;

namespace kratos {

class DependencyVisitor : public IRVisitor {
public:
    DependencyVisitor() : dependency_() {}

    void visit(Generator *generator) override {
        // visit the top and find out top level assignments
        uint64_t stmt_count = generator->stmts_count();
        for (uint64_t i = 0; i < stmt_count; i++) {
            auto const &stmt = generator->get_stmt(i);
            if (stmt->type() == StatementType::Assign) {
                auto assign = stmt->as<AssignStmt>();
                visit_assign(assign.get());
            } else if (stmt->type() == StatementType::Block) {
                auto block = stmt->as<StmtBlock>();
                if (block->block_type() == StatementBlockType::Sequential) {
                    visit_block(block->as<SequentialStmtBlock>().get());
                } else if (block->block_type() == StatementBlockType::Combinational) {
                    visit_block(block->as<CombinationalStmtBlock>().get());
                }
            } else if (stmt->type() == StatementType::ModuleInstantiation) {
                visit_module_instantiation(stmt->as<ModuleInstantiationStmt>().get());
            }
        }
    }
    using DepSet = std::pair<std::unordered_set<Var *>,
                             std::unordered_map<Var *, std::unordered_map<uint32_t, Var *>>>;

    static DepSet get_dep(AssignStmt *stmt) {
        // only interested in the right hand side
        auto var = stmt->right();
        std::unordered_set<Var *> deps;
        std::unordered_map<Var *, std::unordered_map<uint32_t, Var *>> linked_deps;
        get_var_deps(var, deps, linked_deps);
        return {deps, linked_deps};
    }

    const std::unordered_map<Var *, std::unordered_set<Stmt *>> &dependency() const {
        return dependency_;
    }

    const std::unordered_map<Var *, std::unordered_map<uint32_t, Var *>> &linked_dependency()
        const {
        return linked_dependency_;
    }

private:
    std::unordered_map<Var *, std::unordered_set<Stmt *>> dependency_;
    std::unordered_map<Var *, std::unordered_map<uint32_t, Var *>> linked_dependency_;

    void visit_block(CombinationalStmtBlock *block) {
        CombinationBlockVisitor visitor;
        visitor.visit_root(block);
        auto const &vars = visitor.vars();
        for (auto const &var : vars) dependency_[var].emplace(block);
        linked_dependency_.insert(visitor.linked_vars().begin(), visitor.linked_vars().end());
    }

    void visit_block(SequentialStmtBlock *block) {
        auto &lst = block->get_conditions();
        for (auto const &iter : lst) {
            dependency_[iter.second.get()].emplace(block);
        }
    }

    void visit_assign(AssignStmt *assign) {
        auto const &[dep, linked] = get_dep(assign);
        for (auto const &v : dep) dependency_[v].emplace(assign);
        linked_dependency_.insert(linked.begin(), linked.end());
    }

    void visit_module_instantiation(ModuleInstantiationStmt *stmt) {
        auto connection_stmts = stmt->connection_stmt();
        for (auto const &assign : connection_stmts) {
            visit_assign(assign);
        }
    }

    void static get_var_deps(
        Var *var, std::unordered_set<Var *> &dep,
        std::unordered_map<Var *, std::unordered_map<uint32_t, Var *>> &linked_dep) {
        switch (var->type()) {
            case VarType::Base:
            case VarType::PortIO: {
                dep.emplace(var);
                break;
            }
            case VarType ::Expression: {
                auto const &expr = reinterpret_cast<Expr *>(var);
                get_var_deps(expr->left, dep, linked_dep);
                if (expr->right) {
                    get_var_deps(expr->right, dep, linked_dep);
                }
                break;
            }
            case VarType::BaseCasted:
            case VarType ::Slice: {
                // compute linked dependency
                compute_linked_dep(reinterpret_cast<VarSlice *>(var), linked_dep);
                dep.emplace(var);
                break;
            }
            default: {
                // do nothing
            }
        }
    }

    static void compute_linked_dep(
        VarSlice *slice,
        std::unordered_map<Var *, std::unordered_map<uint32_t, Var *>> &linked_dep) {
        auto var_high = slice->var_high();
        auto var_low = slice->var_low();
        auto root = const_cast<Var *>(slice->get_var_root_parent());
        for (uint32_t i = var_low; i <= var_high; i++) {
            linked_dep[root].emplace(i, slice);
        }
        // if indexed by a var
        if (slice->sliced_by_var()) {
            auto var_slice = reinterpret_cast<VarVarSlice *>(slice);
            auto p = var_slice->sliced_var();
            var_high = p->var_high();
            var_low = p->var_low();
            root = const_cast<Var *>(p->get_var_root_parent());
            for (uint32_t i = var_low; i <= var_high; i++) {
                linked_dep[root].emplace(i, slice);
            }
        }
    }

    class CombinationBlockVisitor : public IRVisitor {
    public:
        void visit(IfStmt *stmt) override {
            auto predicate = stmt->predicate();
            auto parent_var = predicate->get_var_root_parent();
            vars_.emplace(const_cast<Var *>(parent_var));
        }

        void visit(SwitchStmt *stmt) override {
            auto target = stmt->target();
            auto parent_var = target->get_var_root_parent();
            vars_.emplace(const_cast<Var *>(parent_var));
        }

        void visit(AssignStmt *stmt) override {
            auto const &[dep, linked] = DependencyVisitor::get_dep(stmt);
            for (auto const &var : dep) vars_.emplace(var);
            linked_vars_.insert(linked.begin(), linked.end());
        }

        std::unordered_set<Var *> &vars() { return vars_; }
        std::unordered_map<Var *, std::unordered_map<uint32_t, Var *>> &linked_vars() {
            return linked_vars_;
        }

    private:
        std::unordered_set<Var *> vars_;
        std::unordered_map<Var *, std::unordered_map<uint32_t, Var *>> linked_vars_;
    };
};

Simulator::Simulator(kratos::Generator *generator) {
    // fix the assignment type
    fix_assignment_type(generator);
    // compute the dependency
    DependencyVisitor visitor;
    // visit in parallel to build up and dep table
    visitor.visit_generator_root_p(generator);
    dependency_ = visitor.dependency();
    linked_dependency_ = visitor.linked_dependency();
    init_pull_up_value(generator);
}

std::optional<uint64_t> Simulator::get_value_(kratos::Var *var) const {
    if (!var) return std::nullopt;
    // only scalar
    if (var->size().size() != 1 || var->size().front() > 1) return std::nullopt;

    if (var->type() == VarType::Parameter) {
        auto param = var->as<Param>();
        return param->value();
    } else if (var->type() == VarType::ConstValue) {
        auto const_ = var->as<Const>();
        return const_->value();
    } else if (var->type() == VarType::Expression) {
        auto result = eval_expr(var);
        if (result) {
            return (*result)[0];
        } else {
            return std::nullopt;
        }
    } else if (var->type() == VarType::Slice) {
        auto root = const_cast<Var *>(var->get_var_root_parent());
        std::vector<uint64_t> values;
        if (root->type() == VarType::ConstValue || root->type() == VarType::Parameter) {
            auto value = get_value_(var);
            if (!value)
                throw InternalException(
                    ::format("Unable to get value for {0}", var->handle_name()));
            values = {*value};
        } else if (root->size().size() == 1 && root->size().front() == 1) {
            // this is size one
            auto value = get_value_(root);
            if (!value) return std::nullopt;
            values = {*value};
        } else if (complex_values_.find(root) == complex_values_.end()) {
            return std::nullopt;
        } else {
            values = complex_values_.at(root);
        }
        // obtain the index
        auto index = get_slice_index(var);
        if (index.empty()) return std::nullopt;
        auto const [var_high, var_low] = compute_var_high_low(root, index);
        if (var_high + 1 - var_low > root->width())
            throw InternalException("Unable to resolve variable slicing");
        auto base = var_low / root->var_width();
        auto low = var_low % root->var_width();
        auto high = var_high % root->var_width();
        auto value = values[base];
        return (value >> low) & (~(0xFFFFFFFFFFFFFFFF << (high + 1)));
    } else {
        if (values_.find(var) == values_.end())
            return std::nullopt;
        else
            return values_.at(var);
    }
}

void Simulator::set_value_(kratos::Var *var, std::optional<uint64_t> op_value) {
    if (!op_value) return;
    auto value = *op_value;
    if (var->size().size() != 1 || var->size().front() != 1) {
        set_complex_value_(var, std::vector<uint64_t>{value});
        return;
    }
    if (var->type() == VarType::Parameter || var->type() == VarType::ConstValue) {
        throw UserException(::format("Cannot set value for constant {0}", var->handle_name()));
    } else if (var->type() == VarType::Slice) {
        auto root = const_cast<Var *>(var->get_var_root_parent());
        std::vector<uint64_t *> values;
        if (root->type() == VarType::ConstValue || root->type() == VarType::Parameter) {
            throw UserException(::format("Cannot set value for constant {0}", var->handle_name()));
        } else if (root->size().size() == 1 && root->size().front() == 1) {
            // this is size one
            if (values_.find(root) == values_.end()) values_[root] = 0;
            values = {&values_.at(root)};
        } else {
            uint32_t base = 1;
            for (uint32_t s : root->size()) {
                base *= s;
            }
            if (complex_values_.find(root) == complex_values_.end()) {
                // fill in values
                std::vector<uint64_t> v(base);
                for (uint64_t i = 0; i < base; i++) v[i] = 0;
                complex_values_.emplace(root, v);
            }
            std::vector<uint64_t> &v_ref = complex_values_.at(root);
            values.reserve(base);
            for (uint64_t i = 0; i < base; i++) values.emplace_back(&v_ref[i]);
        }
        // obtain the index
        auto index = get_slice_index(var);
        if (index.empty()) throw InternalException("Empty slice");
        auto [var_high, var_low] = compute_var_high_low(root, index);
        if (var_high + 1 - var_low > root->width())
            throw InternalException("Unable to resolve variable slicing");
        auto base = var_low / root->var_width();
        var_high = var_high - base * root->var_width();
        var_low = var_low - base * root->var_width();
        auto v = values[base];
        auto temp = *v;
        // compute the mask
        uint64_t mask = (0xFFFFFFFFFFFFFFFF >> (var_high + 1)) >> var_low;
        *v = *v & (~mask);
        value = value & (0xFFFFFFFFFFFFFFFF >> (var_high - var_low + 1));
        *v = *v | (value << var_low);
        if (*v != temp) {
            std::unordered_set<uint32_t> changed_bits;
            uint64_t m = (*v) ^ temp;
            for (uint32_t bit = 0; bit < root->width(); bit++) {
                if ((m >> bit) & 1u) {
                    changed_bits.emplace(bit);
                }
            }
            trigger_event(root, changed_bits);
        }
    } else {
        std::unordered_set<uint32_t> changed_bits;
        if (values_.find(var) != values_.end()) {
            auto temp = values_.at(var);
            if (temp != value) {
                values_[var] = value;
                uint64_t m = value ^ temp;
                for (uint32_t bit = 0; bit < var->width(); bit++) {
                    if ((m >> bit) & 1u) {
                        changed_bits.emplace(bit);
                    }
                }
            }
        } else {
            values_[var] = value;
            for (uint32_t i = 0; i < var->width(); i++) changed_bits.emplace(i);
        }
        trigger_event(var, changed_bits);
    }
}

std::optional<std::vector<uint64_t>> Simulator::get_complex_value_(kratos::Var *var) const {
    if (!var) return std::nullopt;
    if (var->size().size() == 1 && var->size().front() == 1) {
        // this is a scalar
        auto v = get_value_(var);
        if (v)
            return std::vector<uint64_t>{*v};
        else
            return std::nullopt;
    }
    if (var->type() == VarType::Slice) {
        auto slice = var->as<VarSlice>();
        auto root = const_cast<Var *>(var->get_var_root_parent());
        auto index = get_slice_index(var);
        if (index.empty()) return std::nullopt;
        auto const [var_high, var_low] = compute_var_high_low(root, index);
        if (var_low % root->var_width() != 0 ||
            (var_high % root->var_width() != root->var_width() - 1))
            throw InternalException("Misaligned vector slicing");
        if (complex_values_.find(root) == complex_values_.end()) return std::nullopt;
        auto values = complex_values_.at(root);
        // compute the slice range
        auto low = var_low / root->var_width();
        auto high = var_high / root->var_width();
        return std::vector<uint64_t>(values.begin() + low, values.end() + high + 1);
    } else {
        if (complex_values_.find(var) == complex_values_.end()) return std::nullopt;
        return complex_values_.at(var);
    }
}

void Simulator::set_complex_value_(kratos::Var *var,
                                   const std::optional<std::vector<uint64_t>> &op_value) {
    if (!op_value) return;
    auto value = *op_value;
    if (var->size().size() == 1 && var->size().front() == 1) {
        if (value.size() > 1) throw UserException("Cannot set multiple values to a scalar");
        set_value_(var, value[0]);
        return;
    }
    std::vector<uint64_t *> values;
    uint64_t base = 1;
    Var *fill_var;
    uint32_t low, high;
    if (var->type() == VarType::Slice) {
        auto slice = var->as<VarSlice>();
        auto root = const_cast<Var *>(var->get_var_root_parent());
        fill_var = root;
        auto index = get_slice_index(var);
        if (index.empty()) throw InternalException("Empty slice");
        auto const [var_high, var_low] = compute_var_high_low(root, index);
        if (var_low % root->var_width() != 0 ||
            (var_high % root->var_width() != root->var_width() - 1))
            throw InternalException("Misaligned vector slicing");
        low = var_low;
        high = var_high;
        if (root->size().size() == 1 && root->size().front() == 1) {
            // this is size one
            if (values_.find(root) == values_.end()) values_[root] = 0;
            values = {&values_.at(root)};
        } else {
            for (uint32_t s : root->size()) {
                base *= s;
            }
            std::vector<uint64_t> &v_ref = complex_values_.at(root);
            values.reserve(base);
            for (uint64_t i = 0; i < base; i++) values.emplace_back(&v_ref[i]);
        }
    } else {
        for (uint32_t s : var->size()) {
            base *= s;
        }
        fill_var = var;
        low = 0;
        high = base - 1;
    }
    bool fill_in = false;
    if (complex_values_.find(fill_var) == complex_values_.end()) {
        // whatever bits changed
        // fill in values
        fill_in = true;
        if (complex_values_.find(fill_var) == complex_values_.end()) {
            // fill in values
            std::vector<uint64_t> v(base);
            for (uint64_t i = 0; i < base; i++) v[i] = 0;
            complex_values_.emplace(var, v);
        }
    }

    // get values
    if (var->type() != VarType::Slice) {
        values.reserve(base);
        auto &v_ref = complex_values_.at(var);
        for (uint64_t i = 0; i < base; i++) values.emplace_back(&v_ref[i]);
    }

    if (values.size() != value.size()) throw UserException("Misaligned slicing");
    std::unordered_set<uint32_t> changed_bits;
    uint32_t var_width = fill_var->var_width();

    for (uint32_t i = low; i <= high; i++) {
        if (*(values[i]) != value[i] || fill_in) {
            uint32_t bit_mask = (*values[i]) ^ value[i];
            *(values[i]) = value[i];
            for (uint32_t bit = 0; bit < var_width; bit++) {
                if ((bit_mask >> bit) & 1u || fill_in) {
                    changed_bits.emplace(bit + var_width * i);
                }
            }
        }
    }
    trigger_event(fill_var, changed_bits);
}

std::vector<std::pair<uint32_t, uint32_t>> Simulator::get_slice_index(Var *var) const {
    if (var->type() != VarType::Slice) {
        return {};
    }
    auto slice = var->as<VarSlice>();
    auto result = get_slice_index(slice->parent_var);
    uint32_t high, low;
    if (slice->sliced_by_var()) {
        auto var_slice = slice->as<VarVarSlice>();
        auto v = var_slice->sliced_var();
        auto index = get_value_(v);
        // the index variable is empty
        if (!index) {
            return {};
        }
        high = *index;
        low = *index;
    } else {
        high = slice->high;
        low = slice->low;
    }
    result.emplace_back(std::make_pair(high, low));
    return result;
}

void Simulator::trigger_event(kratos::Var *var, const std::unordered_set<uint32_t> &bits_mask) {
    if (bits_mask.empty()) return;

    if (dependency_.find(var) != dependency_.end()) {
        auto const &deps = dependency_.at(var);
        for (auto const &stmt : deps) {
            if (scope_.find(stmt) == scope_.end()) event_queue_.emplace(std::make_pair(var, stmt));
        }
    }

    auto root = const_cast<Var *>(var->get_var_root_parent());
    if (linked_dependency_.find(root) != linked_dependency_.end()) {
        auto const &vars = linked_dependency_.at(root);
        std::unordered_set<Var *> vs;
        for (auto &[bit, v] : vars) {
            if (bits_mask.find(bit) != bits_mask.end()) vs.emplace(v);
        }

        for (auto const &v : vs) {
            if (dependency_.find(v) != dependency_.end()) {
                auto const &deps = dependency_.at(v);
                for (auto const &stmt : deps) {
                    if (scope_.find(stmt) == scope_.end())
                        event_queue_.emplace(std::make_pair(var, stmt));
                }
            }
        }
    }

    // trigger linked events as well
    simulation_depth_++;
}

void Simulator::eval() {
    simulation_depth_ = 0;
    while (!event_queue_.empty()) {
        if (simulation_depth_ > MAX_SIMULATION_DEPTH) {
            throw UserException("Simulation doesn't converge");
        }
        auto &[var, stmt] = event_queue_.front();
        event_queue_.pop();
        process_stmt(stmt, var);
    }
    scope_.clear();
}

std::optional<uint64_t> Simulator::get(kratos::Var *var) const { return get_value_(var); }

std::optional<std::vector<uint64_t>> Simulator::get_array(kratos::Var *var) const {
    return get_complex_value_(var);
}

void Simulator::set(kratos::Var *var, std::optional<uint64_t> value) {
    set_value_(var, value);
    eval();
}

void Simulator::set_i(kratos::Var *var, std::optional<int64_t> value) {
    if (value) {
        auto v = *value;
        auto u_v = *(reinterpret_cast<uint64_t *>(&v));
        u_v = truncate(u_v, var->width());
        set_value_(var, u_v);
        eval();
    }
}

void Simulator::set(kratos::Var *var, const std::optional<std::vector<uint64_t>> &value) {
    set_complex_value_(var, value);
    eval();
}

void Simulator::set_i(kratos::Var *var, const std::optional<std::vector<int64_t>> &value) {
    if (value) {
        auto vs = *value;
        std::vector<uint64_t> u_vs;
        u_vs.reserve(vs.size());
        for (auto v : vs) {
            auto u_v = *(reinterpret_cast<uint64_t *>(v));
            u_v = truncate(u_v, var->width());
            u_vs.emplace_back(u_v);
        }
        set_complex_value_(var, u_vs);
        eval();
    }
}

void Simulator::process_stmt(kratos::Stmt *stmt, Var *var) {
    switch (stmt->type()) {
        case StatementType::Assign: {
            auto assign = reinterpret_cast<AssignStmt *>(stmt);
            process_stmt(assign, var);
            break;
        }
        case StatementType::Block: {
            auto block = reinterpret_cast<StmtBlock *>(stmt);
            if (block->block_type() == StatementBlockType::Combinational) {
                process_stmt(reinterpret_cast<CombinationalStmtBlock *>(block), var);
            } else if (block->block_type() == StatementBlockType::Sequential) {
                process_stmt(reinterpret_cast<SequentialStmtBlock *>(block), var);
            } else {
                process_stmt(block, var);
            }
            break;
        }
        case StatementType::If: {
            auto if_ = reinterpret_cast<IfStmt *>(stmt);
            process_stmt(if_, var);
            break;
        }
        case StatementType::Switch: {
            auto switch_ = reinterpret_cast<SwitchStmt *>(stmt);
            process_stmt(switch_, var);
            break;
        }
        default:
            throw std::runtime_error("Not implemented");
    }
}

void Simulator::process_stmt(kratos::AssignStmt *stmt, Var *) {
    auto right = stmt->right();
    auto val = eval_expr(right);
    if (val) {
        if (stmt->assign_type() != AssignmentType::NonBlocking)
            set_complex_value_(stmt->left(), val);
        else
            nba_values_.emplace(stmt->left(), *val);
    }
}

void Simulator::process_stmt(kratos::StmtBlock *block, Var *var) {
    for (auto &stmt : *block) {
        process_stmt(stmt.get(), var);
    }
}

void Simulator::process_stmt(kratos::CombinationalStmtBlock *block, Var *var) {
    scope_.emplace(block);
    process_stmt(reinterpret_cast<StmtBlock *>(block), var);
    scope_.erase(block);
}

void Simulator::process_stmt(kratos::IfStmt *if_, Var *var) {
    auto target = if_->predicate();
    auto val = get_value_(target.get());
    if (val && (*val)) {
        auto const &then_ = if_->then_body();
        process_stmt(then_.get(), var);
    } else {
        auto const &else_ = if_->else_body();
        process_stmt(else_.get(), var);
    }
}

void Simulator::process_stmt(kratos::SwitchStmt *switch_, Var *var) {
    auto target = switch_->target().get();
    auto val = get_value_(target);
    auto const &body = switch_->body();
    if (!val) {
        // go to default case
        if (body.find(nullptr) != body.end()) {
            auto stmt = body.at(nullptr);
            process_stmt(stmt.get(), var);
        }
    } else {
        auto value = *val;
        for (auto const &[cond, stmt] : body) {
            // we compare bits
            int64_t cond_val = cond->value();
            int64_t *v_p = &cond_val;
            uint64_t bits = *(reinterpret_cast<uint64_t *>(v_p));
            bits &= (0xFFFFFFFFFFFFFFFF >> target->width());
            if (value == bits) {
                process_stmt(stmt.get(), var);
                return;
            }
        }
        // default case
        if (body.find(nullptr) != body.end()) {
            auto stmt = body.at(nullptr);
            process_stmt(stmt.get(), var);
        }
    }
}

void Simulator::process_stmt(kratos::SequentialStmtBlock *block, Var *var_) {
    // only trigger it if it's actually high/low
    auto const &conditions = block->get_conditions();
    bool trigger = false;
    for (auto const &[edge, var] : conditions) {
        if (var.get() != var_) continue;
        if (edge == BlockEdgeType::Posedge) {
            auto val = get_value_(var.get());
            if (val && *val) {
                trigger = true;
                break;
            }
        } else {
            auto val = get_value_(var.get());
            if (val && (!(*val))) {
                trigger = true;
                break;
            }
        }
    }
    if (!trigger) return;
    process_stmt(reinterpret_cast<StmtBlock *>(block), var_);

    for (auto const &[var, value] : nba_values_) {
        set_complex_value_(var, value);
    }
    // clear the nba regions
    nba_values_.clear();
}

class InitValueVisitor : public IRVisitor {
public:
    explicit InitValueVisitor(std::function<void(AssignStmt *)> fn) : fn_(std::move(fn)) {}

    void visit(Generator *gen) override {
        uint64_t stmt_count = gen->stmts_count();
        for (uint64_t i = 0; i < stmt_count; i++) {
            auto stmt = gen->get_stmt(i);
            if (stmt->type() == StatementType::Assign) {
                auto assign = stmt->as<AssignStmt>();
                if (assign->right()->type() == VarType::ConstValue) {
                    fn_(assign.get());
                }
            }
        }
    }

private:
    std::function<void(AssignStmt *)> fn_;
};

void Simulator::init_pull_up_value(Generator *generator) {
    auto fn = [&](AssignStmt *stmt) { this->process_stmt(stmt, nullptr); };
    InitValueVisitor visitor(fn);
    visitor.visit_generator_root(generator);
}

std::optional<std::vector<uint64_t>> Simulator::eval_expr(kratos::Var *var) const {
    if (var->type() == VarType::Expression) {
        auto expr = reinterpret_cast<Expr *>(var);
        // there are couple special ones
        if (expr->op == ExprOp::Concat) {
            auto var_concat = reinterpret_cast<VarConcat *>(expr);
            auto vars = std::vector<Var *>(var_concat->vars().begin(), var_concat->vars().end());
            std::reverse(vars.begin(), vars.end());
            uint32_t shift_amount = 0;
            uint64_t value = 0;
            for (auto var_ : vars) {
                auto v = get_value_(var_);
                if (v) {
                    value |= (*v) << shift_amount;
                    shift_amount += var_->width();
                } else {
                    return std::nullopt;
                }
            }
            return std::vector<uint64_t>{value};
        } else if (expr->op == ExprOp::Extend) {
            // depends on whether it's a signed value or not
            auto extend = reinterpret_cast<VarExtend *>(var);
            auto base_var = extend->parent_var();
            auto value = get_complex_value_(base_var);
            if (!value) return std::nullopt;
            if (var->is_signed()) {
                // do signed extension
                if ((*value).size() > 1) {
                    throw std::runtime_error("Not implemented");
                }
                auto v = (*value)[0];
                if (v >> (var->width() - 1)) {
                    // do a signed extension
                    for (uint32_t i = base_var->width(); i < var->width(); i++) {
                        v |= 1u << i;
                    }
                }
                return std::vector<uint64_t>{v};
            } else {
                return value;
            }
        } else {
            auto left_val = get_complex_value_(expr->left);
            if (!left_val) return left_val;
            auto right_val = get_complex_value_(expr->right);
            if (!is_unary_op(expr->op)) {
                if (!right_val) return std::nullopt;
                if ((*left_val).size() > 1) throw std::runtime_error("Not implemented");
                if ((*right_val).size() > 1) throw std::runtime_error("Not implemented");
                auto left_value = (*left_val)[0];
                auto right_value = (*right_val)[0];
                auto result = eval_bin_op(left_value, right_value, expr->op, expr->width(),
                                          expr->is_signed());
                return std::vector<uint64_t>{result};
            } else {
                auto left_value = (*left_val)[0];
                auto result = eval_unary_op(left_value, expr->op, expr->width());
                return std::vector<uint64_t>{result};
            }
        }

    } else {
        return get_complex_value_(var);
    }
}

}