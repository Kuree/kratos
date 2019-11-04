#include "sim.hh"
#include "except.hh"
#include "fmt/format.h"
#include "stmt.hh"

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
                auto dep = get_dep(assign.get());
                for (auto const &v: dep)
                    dependency_[v].emplace(stmt.get());
            } else if (stmt->type() == StatementType::Block) {
                auto block = stmt->as<StmtBlock>();
                if (block->block_type() == StatementBlockType::Sequential) {
                    visit_block(block->as<SequentialStmtBlock>().get());
                } else if (block->block_type() == StatementBlockType::Combinational) {
                    visit_block(block->as<CombinationalStmtBlock>().get());
                }
            }
        }
    }

    void visit_block(CombinationalStmtBlock *block) {
        CombinationBlockVisitor visitor;
        visitor.visit_root(block);
        auto const &vars = visitor.vars();
        for (auto const &var : vars) dependency_[var].emplace(block);
    }

    void visit_block(SequentialStmtBlock *block) {
        auto &lst = block->get_conditions();
        for (auto const &iter : lst) {
            dependency_[iter.second.get()].emplace(block);
        }
    }

    static std::unordered_set<Var *> get_dep(AssignStmt *stmt) {
        // only interested in the right hand side
        auto var = stmt->right();
        std::unordered_set<Var *> deps;
        get_var_deps(var, deps);
        return deps;
    }

    const std::unordered_map<Var *, std::unordered_set<Stmt *>> &dependency() const {
        return dependency_;
    }

private:
    std::unordered_map<Var *, std::unordered_set<Stmt *>> dependency_;

    void static get_var_deps(Var *var, std::unordered_set<Var *> &dep) {
        switch (var->type()) {
            case VarType::Base:
            case VarType::PortIO: {
                dep.emplace(var);
                break;
            }
            case VarType ::Expression: {
                auto const &expr = reinterpret_cast<Expr *>(var);
                get_var_deps(expr->left, dep);
                if (expr->right) {
                    get_var_deps(expr->right, dep);
                }
                break;
            }
            case VarType::BaseCasted:
            case VarType ::Slice: {
                auto base = const_cast<Var *>(var->get_var_root_parent());
                get_var_deps(base, dep);
                break;
            }
            default: {
                // do nothing
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
            auto dep = DependencyVisitor::get_dep(stmt);
            for (auto const &var : dep) vars_.emplace(var);
        }

        std::unordered_set<Var *> &vars() { return vars_; }

    private:
        std::unordered_set<Var *> vars_;
    };
};

Simulator::Simulator(kratos::Generator *generator) {
    // compute the dependency
    DependencyVisitor visitor;
    // visit in parallel to build up and dep table
    visitor.visit_generator_root_p(generator);
    dependency_ = visitor.dependency();
}

std::pair<uint32_t, uint32_t> compute_var_high_low(
    Var *root, const std::vector<std::pair<uint32_t, uint32_t>> &index) {
    // outer to inner
    // flatten the index
    auto const &var_sizes = root->size();
    // compute the actual index
    uint32_t index_base = 0;
    uint32_t var_low = 0;
    uint32_t var_high = 0;
    uint32_t index_to_size = 0;
    uint64_t i = 0;
    while (i < index.size()) {
        auto const &[slice_high, slice_low] = index[i];
        if (slice_high > slice_low) {
            index_base += slice_low;
        } else {
            // compute the real index
            uint32_t base = 1;
            index_to_size++;
            // if we have bit slicing, we need to stop
            if (index_to_size >= var_sizes.size()) break;
            for (uint64_t j = index_to_size; j < var_sizes.size(); j++) {
                base *= var_sizes[j];
            }
            var_low += base * slice_low;
            var_high = var_low + (var_high + 1) * base;
        }
        i++;
    }
    // normalize to bits
    var_high *= root->var_width();
    var_low *= root->var_width();

    if (i < index.size()) {
        for (; i < index.size(); i++) {
            auto const &[slice_high, slice_low] = index[i];
            var_low += slice_low;
            var_high = var_low + (slice_high - slice_low);
        }
    }

    return {var_high, var_low};
}

std::optional<uint64_t> Simulator::get_value(kratos::Var *var) const {
    if (!var) return std::nullopt;
    // only scalar
    if (var->size().size() != 1 || var->size().front() > 1) return std::nullopt;

    if (var->type() == VarType::Parameter) {
        auto param = var->as<Param>();
        return param->value();
    } else if (var->type() == VarType::ConstValue) {
        auto const_ = var->as<Const>();
        return const_->value();
    } else if (var->type() == VarType::Slice) {
        auto root = const_cast<Var *>(var->get_var_root_parent());
        std::vector<uint64_t> values;
        if (root->type() == VarType::ConstValue || root->type() == VarType::Parameter) {
            auto value = get_value(var);
            if (!value)
                throw InternalException(
                    ::format("Unable to get value for {0}", var->handle_name()));
            values = {*value};
        } else if (root->size().size() == 1 && root->size().front() == 1) {
            // this is size one
            auto value = get_value(root);
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
        if (var_high + 1 - var_low > root->var_width())
            throw InternalException("Unable to resolve variable slicing");
        auto base = var_low / 64;
        auto value = values[base];
        return (value >> var_low) & (0xFFFFFFFFFFFFFFFF >> (var_high + 1));
    } else {
        if (values_.find(var) == values_.end())
            return std::nullopt;
        else
            return values_.at(var);
    }
}

void Simulator::set_value(kratos::Var *var, std::optional<uint64_t> op_value) {
    if (!op_value) return;
    auto value = *op_value;
    if (var->size().size() != 1 || var->size().front() != 1) {
        set_complex_value(var, std::vector<uint64_t>{value});
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
        auto const [var_high, var_low] = compute_var_high_low(root, index);
        if (var_high + 1 - var_low > root->var_width())
            throw InternalException("Unable to resolve variable slicing");
        auto base = var_low / 64;
        auto v = values[base];
        // compute the mask
        uint64_t mask = (0xFFFFFFFFFFFFFFFF >> (var_high + 1)) >> var_low;
        *v = *v & (~mask);
        value = value & (0xFFFFFFFFFFFFFFFF >> (var_high - var_low + 1));
        *v = *v | (value << var_low);
        trigger_event(root);
    } else {
        values_[var] = value;
        trigger_event(var);
    }
}

std::optional<std::vector<uint64_t>> Simulator::get_complex_value(kratos::Var *var) const {
    if (!var) return std::nullopt;
    if (var->size().size() == 1 && var->size().front() == 1) {
        // this is a scalar
        auto v = get_value(var);
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
        return std::vector<uint64_t>(values.begin() + var_low, values.end() + var_high + 1);
    } else {
        if (complex_values_.find(var) == complex_values_.end()) return std::nullopt;
        return complex_values_.at(var);
    }
}

void Simulator::set_complex_value(kratos::Var *var,
                                  const std::optional<std::vector<uint64_t>> &op_value) {
    if (!op_value) return;
    auto value = *op_value;
    if (var->size().size() == 1 && var->size().front() == 1) {
        if (value.size() > 1) throw UserException("Cannot set multiple values to a scalar");
        set_value(var, value[0]);
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
    if (complex_values_.find(fill_var) == complex_values_.end()) {
        // fill in values
        if (complex_values_.find(fill_var) == complex_values_.end()) {
            // fill in values
            std::vector<uint64_t> v(base);
            for (uint64_t i = 0; i < base; i++) v[i] = 0;
            complex_values_.emplace(var, v);
        }
    }
    if (values.size() != value.size()) throw UserException("Misaligned slicing");
    for (uint32_t i = low; i <= high; i++) {
        *(values[i]) = value[i];
    }
    trigger_event(fill_var);
}

std::vector<std::pair<uint32_t, uint32_t>> Simulator::get_slice_index(Var *var) const {
    std::vector<std::pair<uint32_t, uint32_t>> result;
    if (var->type() != VarType::Slice) {
        return {};
    }
    auto slice = var->as<VarSlice>();
    auto slices = get_slice_index(slice->parent_var);
    uint32_t high, low;
    if (slice->sliced_by_var()) {
        auto var_slice = slice->as<VarVarSlice>();
        auto v = var_slice->sliced_var();
        auto index = get_value(v);
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

void Simulator::trigger_event(kratos::Var *var) {
    if (dependency_.find(var) == dependency_.end()) return;
    auto deps = dependency_.at(var);
    for (auto const &stmt : deps) {
        event_queue_.emplace(stmt);
    }
}

void Simulator::eval() {
    while (!event_queue_.empty()) {
        auto stmt = event_queue_.front();
        event_queue_.pop();
        process_stmt(stmt);
    }
}

void Simulator::process_stmt(kratos::Stmt *stmt) {
    switch (stmt->type()) {
        case StatementType::Assign: {
            auto assign = reinterpret_cast<AssignStmt *>(stmt);
            process_stmt(assign);
            break;
        }
        default:
            throw std::runtime_error("Not implemented");
    }
}

void Simulator::process_stmt(kratos::AssignStmt *stmt) {
    auto right = stmt->right();
    auto val = eval_expr(right);
    if (val) {
        set_complex_value(stmt->left(), val);
    }
}

std::optional<std::vector<uint64_t>> Simulator::eval_expr(kratos::Var *var) {
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
                auto v = get_value(var_);
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
            auto value = get_complex_value(base_var);
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
            auto left_val = get_complex_value(expr->left);
            if (!left_val) return left_val;
            auto right_val = get_complex_value(expr->right);
            if (!is_reduction_op(expr->op)) {
                if (!right_val) return std::nullopt;
                if ((*left_val).size() > 1) throw std::runtime_error("Not implemented");
                if ((*right_val).size() > 1) throw std::runtime_error("Not implemented");
                auto left_value = (*left_val)[0];
                auto right_value = (*right_val)[0];
                uint64_t result;
                switch(expr->op) {
                    case ExprOp::Add: {
                        result = left_value + right_value;
                        break;
                    }
                    case ExprOp::And: {
                        result = left_value & right_value;
                        break;
                    }
                    case ExprOp::Divide: {
                        result = left_value / right_value;
                        break;
                    }
                    case ExprOp::Eq: {
                        result = left_value == right_value;
                        break;
                    }
                    default: {
                        throw std::runtime_error("Not implemented");
                    }
                }
                result = result & ((0xFFFFFFFFFFFFFFFF) >> (64 - var->width()));
                return std::vector<uint64_t>{result};
            } else if (is_reduction_op(expr->op)) {
                throw std::runtime_error("Not implemented");
            } else {
                throw std::runtime_error("Not implemented");
            }
        }

    } else {
        return get_complex_value(var);
    }
}

}