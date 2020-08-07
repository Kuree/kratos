#include "expr.hh"

#include <algorithm>
#include <cassert>
#include <iostream>
#include <queue>
#include <stdexcept>

#include "except.hh"
#include "fmt/format.h"
#include "generator.hh"
#include "interface.hh"
#include "sim.hh"
#include "stmt.hh"
#include "syntax.hh"
#include "util.hh"

using fmt::format;
using std::make_shared;
using std::shared_ptr;
using std::string;
using std::vector;

namespace kratos {

bool is_relational_op(ExprOp op) {
    static std::unordered_set<ExprOp> ops = {ExprOp::LessThan, ExprOp::GreaterThan,
                                             ExprOp::LessEqThan, ExprOp::GreaterEqThan, ExprOp::Eq};
    return ops.find(op) != ops.end();
}

bool is_reduction_op(ExprOp op) {
    static std::unordered_set<ExprOp> ops = {ExprOp::UOr, ExprOp::UXor, ExprOp::UAnd, ExprOp::UNot};
    return ops.find(op) != ops.end();
}

bool is_expand_op(ExprOp op) {
    static std::unordered_set<ExprOp> ops = {ExprOp::Concat, ExprOp::Extend};
    return ops.find(op) != ops.end();
}

bool is_unary_op(ExprOp op) {
    static std::unordered_set<ExprOp> ops = {ExprOp::UXor,  ExprOp::UPlus, ExprOp::UOr,
                                             ExprOp::UNot,  ExprOp::UXor,  ExprOp::UInvert,
                                             ExprOp::UMinus};
    return ops.find(op) != ops.end();
}

uint32_t Var::width() const {
    uint32_t w = param_ ? param()->value() : var_width_;
    for (auto const &i : size_) w *= i;
    return w;
}

Expr &Var::operator-(const Var &var) const {
    return generator()->expr(ExprOp::Minus, const_cast<Var *>(this), const_cast<Var *>(&var));
}

Expr &Var::operator-() const {
    return generator()->expr(ExprOp::Minus, const_cast<Var *>(this), nullptr);
}

Expr &Var::operator~() const {
    return generator()->expr(ExprOp::UInvert, const_cast<Var *>(this), nullptr);
}

Expr &Var::operator+() const {
    return generator()->expr(ExprOp::UPlus, const_cast<Var *>(this), nullptr);
}

Expr &Var::r_or() const {
    auto var = generator()->get_var(name);
    return generator()->expr(ExprOp::UOr, const_cast<Var *>(this), nullptr);
}
Expr &Var::r_and() const {
    auto var = generator()->get_var(name);
    return generator()->expr(ExprOp::UAnd, const_cast<Var *>(this), nullptr);
}
Expr &Var::r_xor() const {
    auto var = generator()->get_var(name);
    return generator()->expr(ExprOp::UXor, const_cast<Var *>(this), nullptr);
}
Expr &Var::r_not() const {
    auto var = generator()->get_var(name);
    return generator()->expr(ExprOp::UNot, const_cast<Var *>(this), nullptr);
}

Expr &Var::operator+(const Var &var) const {
    return generator()->expr(ExprOp::Add, const_cast<Var *>(this), const_cast<Var *>(&var));
}

Expr &Var::operator*(const Var &var) const {
    return generator()->expr(ExprOp::Multiply, const_cast<Var *>(this), const_cast<Var *>(&var));
}

Expr &Var::operator%(const Var &var) const {
    return generator()->expr(ExprOp::Mod, const_cast<Var *>(this), const_cast<Var *>(&var));
}

Expr &Var::operator/(const Var &var) const {
    return generator()->expr(ExprOp::Divide, const_cast<Var *>(this), const_cast<Var *>(&var));
}

Expr &Var::operator>>(const Var &var) const {
    return generator()->expr(ExprOp::LogicalShiftRight, const_cast<Var *>(this),
                             const_cast<Var *>(&var));
}

Expr &Var::operator<<(const Var &var) const {
    return generator()->expr(ExprOp::ShiftLeft, const_cast<Var *>(this), const_cast<Var *>(&var));
}

Expr &Var::operator|(const Var &var) const {
    return generator()->expr(ExprOp::Or, const_cast<Var *>(this), const_cast<Var *>(&var));
}

Expr &Var::operator&(const Var &var) const {
    return generator()->expr(ExprOp::And, const_cast<Var *>(this), const_cast<Var *>(&var));
}

Expr &Var::operator^(const Var &var) const {
    return generator()->expr(ExprOp::Xor, const_cast<Var *>(this), const_cast<Var *>(&var));
}

Expr &Var::ashr(const Var &var) const {
    return generator()->expr(ExprOp::SignedShiftRight, const_cast<Var *>(this),
                             const_cast<Var *>(&var));
}

Expr &Var::operator<(const Var &var) const {
    return generator()->expr(ExprOp::LessThan, const_cast<Var *>(this), const_cast<Var *>(&var));
}

Expr &Var::operator>(const Var &var) const {
    return generator()->expr(ExprOp::GreaterThan, const_cast<Var *>(this), const_cast<Var *>(&var));
}

Expr &Var::operator<=(const Var &var) const {
    return generator()->expr(ExprOp::LessEqThan, const_cast<Var *>(this), const_cast<Var *>(&var));
}

Expr &Var::operator>=(const Var &var) const {
    return generator()->expr(ExprOp::GreaterEqThan, const_cast<Var *>(this),
                             const_cast<Var *>(&var));
}

Expr &Var::eq(const Var &var) const {
    return generator()->expr(ExprOp::Eq, const_cast<Var *>(this), const_cast<Var *>(&var));
}

Expr &Var::operator!=(const Var &var) const {
    return generator()->expr(ExprOp::Neq, const_cast<Var *>(this), const_cast<Var *>(&var));
}

Expr &Var::operator&&(const Var &var) const {
    return generator()->expr(ExprOp::LAnd, const_cast<Var *>(this), const_cast<Var *>(&var));
}

Expr &Var::operator||(const Var &var) const {
    return generator()->expr(ExprOp::LOr, const_cast<Var *>(this), const_cast<Var *>(&var));
}

Expr &Var::pow(const Var &var) const {
    return generator()->expr(ExprOp::Power, const_cast<Var *>(this), const_cast<Var *>(&var));
}

VarSlice &Var::operator[](std::pair<uint32_t, uint32_t> slice) {
    auto const [high, low] = slice;
    if (low > high) {
        throw VarException(::format("low ({0}) cannot be larger than ({1})", low, high), {this});
    }
    // if the size is not 1, we are slicing off size, not width
    if (size_.size() == 1 && size_.front() == 1) {
        if (high >= width()) {
            throw VarException(
                ::format("high ({0}) has to be smaller than width ({1})", high, width()), {this});
        }
    } else {
        if (high > size_.front()) {
            throw VarException(
                ::format("high ({0}) has to be smaller than size ({1})", high, size_.front()),
                {this});
        }
    }
    // if there is one already
    for (auto const &s : slices_) {
        if (!s->sliced_by_var()) {
            if (high == s->high && low == s->low) return *s;
        }
    }
    // create a new one
    // notice that slice is not part of generator's variables. It's handled by the parent (var)
    // itself
    // depends on the root variable, if it is actually a struct, we need to return to the
    // actual trampoline class as proxy
    auto var_root = get_var_root_parent();
    std::shared_ptr<VarSlice> var_slice = ::make_shared<VarSlice>(this, high, low);
    if (var_root->is_struct() && var_slice->width() == var_slice->var_width()) {
        // we actually reached the real struct
    }
    slices_.emplace_back(var_slice);
    return *var_slice;
}

VarSlice &Var::operator[](const std::shared_ptr<Var> &var) {
    // if there is one already
    for (auto const &s : slices_) {
        if (s->sliced_by_var()) {
            auto const s_ = s->as<VarVarSlice>();
            if (s_->sliced_var() == var.get()) return *s_;
        }
    }
    auto var_slice = ::make_shared<VarVarSlice>(this, var.get());
    slices_.emplace_back(var_slice);
    return *var_slice;
}

VarConcat &Var::concat(Var &var) {
    auto *ptr = &var;
    // notice that we effectively created an implicit sink->sink by creating a concat
    // however, it's not an assignment, that's why we need to use concat_vars to hold the
    // vars
    for (auto const &exist_var : concat_vars_) {
        // reuse the existing variables
        if (exist_var->vars().size() == 2 && exist_var->vars().back() == ptr) {
            return *exist_var;
        }
    }
    auto concat_ptr = std::make_shared<VarConcat>(shared_from_this(), ptr->shared_from_this());
    concat_vars_.emplace(concat_ptr);
    return *concat_ptr;
}

VarExtend &Var::extend(uint32_t width) {
    if (extended_.find(width) != extended_.end()) {
        return *extended_.at(width);
    } else {
        auto p = std::make_shared<VarExtend>(shared_from_this(), width);
        extended_.emplace(width, p);
        return *p;
    }
}

std::string Var::to_string() const { return name; }

uint64_t Var::child_count() {
    // get linked vars
    return slices_.size();
}

IRNode *Var::get_child(uint64_t index) {
    if (index < child_count()) {
        return slices_[index].get();
    }
    return nullptr;
}

std::string Var::handle_name() const { return handle_name(false); }

std::string Var::handle_name(bool ignore_top) const {
    auto gen_name = generator()->handle_name(ignore_top);
    if (!gen_name.empty())
        return ::format("{0}.{1}", generator()->handle_name(ignore_top), to_string());
    else
        return to_string();
}

std::string Var::handle_name(kratos::Generator *scope) const {
    // subtract the scope
    auto gen_name = scope->handle_name();
    auto var_name = handle_name();
    auto pos = var_name.find(gen_name);
    if (pos != 0) {
        throw VarException(
            ::format("{0} is not accessible from {1}", gen_name, generator()->handle_name()),
            {this, scope, this->generator()});
    }
    // we +1 because there is a dot there
    return var_name.substr(pos + gen_name.size() + 1);
}

void Var::set_width_param(const std::shared_ptr<Param> &param) { set_width_param(param.get()); }

void Var::set_width_param(kratos::Param *param) {
    // set width to the current param value
    if (param->value() <= 0) {
        throw VarException(::format("{0} is non-positive ({1}), "
                                    "thus cannot be used for parametrization width",
                                    param->to_string(), param->value()),
                           {param});
    }
    var_width_ = param->value();
    param_ = param;
    param->add_param_width_var(this);
}

VarSlice &Var::operator[](uint32_t bit) { return this->operator[]({bit, bit}); }

class ParamVisitor : public IRVisitor {
public:
    void visit(Param *param) override { params_.emplace(param); }
    const std::unordered_set<Param *> &params() const { return params_; }

private:
    std::unordered_set<Param *> params_;
};

void Var::set_size_param(uint32_t index, Var *param) {
    if (type_ != VarType::Base && type_ != VarType::PortIO)
        throw UserException(::format("{0} is not a variable or port", to_string()));
    if (index >= size_.size())
        throw UserException(::format("{0} does not have {1} dimension", to_string(), index));

    // static evaluate the expression using built-in simulator
    Simulator sim(nullptr);
    auto result = sim.eval_expr(param);
    // sanity check, no coverage
    // LCOV_EXCL_START
    if (!result || (*result).size() != 1)
        throw UserException(::format("Unable to static elaborate value {0}", param->to_string()));
    auto new_dim_size_i = static_cast<int64_t>((*result)[0]);
    if (new_dim_size_i <= 0)
        throw UserException(::format("Unable to static elaborate value {0}", param->to_string()));
    auto new_dim_size = static_cast<uint64_t>(new_dim_size_i);
    // LCOV_EXCL_STOP
    for (auto const &slice : slices_) {
        if (!slice->sliced_by_var()) {
            auto slice_index = slice->get_slice_index();
            if (slice_index.size() > index) {
                auto [high, low] = slice_index[index];
                if (high >= new_dim_size || low >= new_dim_size)
                    throw VarException(
                        ::format("Unable to parameterize dim {0} due to usage of {1}", index,
                                 slice->to_string()),
                        {slice.get(), this});
            }
        }
    }
    // all good. now we need to resize the index
    size_[index] = new_dim_size;
    size_param_[index] = param;

    // get all the parameters
    ParamVisitor visitor;
    visitor.visit_root(param);
    auto const &params = visitor.params();
    for (const auto &p : params) {
        p->add_param_size_var(this, index, param);
    }
}

Var &copy_var_const_parm(Var *var, Generator *parent) {
    if (var->is_param()) {
        auto param = var->as<Param>();
        const auto *param_parent = param->parent_param();
        if (!param_parent || param_parent->generator() != parent)
            throw UserException(
                ::format("Unable to copy var definition since the width parametrization is not set "
                         "in parent"));
        return *const_cast<Param *>(param_parent);
    } else if (var->type() == VarType::ConstValue) {
        auto c = var->as<Const>();
        auto &c_ = constant(c->value(), c->width(), c->is_signed());
        c_.set_generator(parent);
        return c_;
    } else {
        if (var->type() != VarType::Expression)
            throw UserException("Only expression with constant and parameters allowed");
        auto expr = var->as<Expr>();
        auto &left = copy_var_const_parm(expr->left, parent);
        if (expr->right) {
            auto &right = copy_var_const_parm(expr->right, parent);
            return parent->expr(expr->op, &left, &right);
        } else {
            return parent->expr(expr->op, &left, nullptr);
        }
    }
}

void Var::copy_meta_data(Var *new_var) const {
    // basically the parameters
    if (param_) {
        const auto *parent_param = param_->parent_param();
        if (!parent_param || parent_param->generator() != new_var->generator()) {
            throw UserException(::format(
                ::format("Unable to copy var definition since the width parametrization is set to "
                         "different generator for var {0}",
                         to_string())));
        }
        new_var->param_ = const_cast<Param *>(parent_param);
    }
    // need to copy size as well
    // notice that size parameters are actually expressions, so we need to copy all the expressions
    // over using ast visitor
    for (const auto &[index, v] : size_param_) {
        try {
            auto &new_v = copy_var_const_parm(v, new_var->generator());
            new_var->set_size_param(index, &new_v);
        } catch (UserException &) {
            continue;
        }
    }
}

uint32_t num_size_decrease(Var *var) {
    if (var->type() == VarType::Slice) {
        auto *slice = reinterpret_cast<VarSlice *>(var);
        auto *parent = slice->parent_var;
        auto diff = parent->size().size() - slice->size().size();
        if (parent->type() == VarType::Slice) {
            return diff + num_size_decrease(reinterpret_cast<VarSlice *>(parent));
        } else {
            // base case 1
            return diff;
        }
    }
    // base case 0
    return 0;
}

VarSlice::VarSlice(Var *parent, uint32_t high, uint32_t low)
    : Var(parent->generator(), "", parent->var_width(), 1, parent->is_signed(), VarType::Slice),
      parent_var(parent),
      low(low),
      high(high),
      op_({high, low}) {
    // compute the width
    // notice that if the user has explicit set it to be an array
    // we need to honer their wish
    // we also need to honer the way the dimension the array is set
    auto diff = num_size_decrease(parent);
    auto diff_parent = true;
    if (low == 0 && high == 0 && parent->type() == VarType::Slice) {
        auto p_d = num_size_decrease(reinterpret_cast<VarSlice *>(parent)->parent_var);
        diff_parent = diff != p_d;
    }
    bool dropped_dim_size1 = low == 0 && high == 0 &&
                             parent->get_var_root_parent()->size().size() > 1 &&
                             parent->get_var_root_parent()->size().back() == 1 && diff_parent &&
                             diff == parent->get_var_root_parent()->size().size() - 1;
    if (parent->size().size() == 1 && parent->size().front() == 1 && parent->explicit_array()) {
        if (high != 0 || low != 0) {
            throw VarException(::format("Parent {0} is a scalar but used marked as an explicit "
                                        "array, only [0, 0] allowed",
                                        parent->to_string()),
                               {parent});
        }
    } else if (parent->size().size() == 1 && parent->size().front() == 1 && !dropped_dim_size1) {
        // even it is true, we still need to make sure cases such as
        // [3:0][0:0] declaration (from size = (4, 1)), can be sliced twice before hitting
        // the wire, which means we need to count the number of size decreases
        // this is the actual slice
        var_width_ = high - low + 1;
        is_packed_ = false;
    } else if (parent->size().size() == 1 && parent->size().front() == 1 && dropped_dim_size1) {
        // need to keep the var width calculation correct
        var_width_ = parent->var_width();
        is_packed_ = false;
    } else {
        if (high == low) {
            if (parent->size().size() == 1) {
                size_ = {1};
                is_packed_ = false;
            } else {
                size_ = std::vector<uint32_t>(parent->size().begin() + 1, parent->size().end());
                is_packed_ = parent->is_packed();
            }
            var_width_ = parent->var_width();
        } else {
            // readjust the top slice
            size_ = std::vector<uint32_t>(parent->size().begin(), parent->size().end());
            size_.back() = high - low + 1;
            var_width_ = parent->var_width();
            is_packed_ = parent->is_packed();
        }
    }
    // compute the var high and var_low
    if (parent->type() != VarType::Slice) {
        // use width to compute
        // honer user's wish
        if (parent->size().size() == 1 && parent->size().front() == 1 && parent->explicit_array()) {
            var_low_ = 0;
            var_high_ = var_width_ - 1;
        } else if (parent->size().size() == 1 && parent->size().front() == 1) {
            var_low_ = low;
            var_high_ = high;
        } else {
            uint32_t base_width = parent->var_width();
            for (uint64_t i = 1; i < parent->size().size(); i++) base_width *= parent->size()[i];
            var_low_ = low * base_width;
            var_high_ = (high + 1) * base_width - 1;
        }
    } else {
        // it's a slice
        auto *slice = dynamic_cast<VarSlice *>(parent);
        if (parent->size().size() == 1 && parent->size().front() == 1 && !dropped_dim_size1) {
            var_low_ = low + slice->var_low();
            var_high_ = (high + 1) + slice->var_low() - 1;
        } else if (parent->size().size() == 1 && parent->size().front() == 1 && dropped_dim_size1) {
            var_low_ = slice->var_low();
            var_high_ = slice->var_high();
        } else {
            uint32_t base_width = parent->var_width();
            for (uint64_t i = 1; i < parent->size().size(); i++) base_width *= parent->size()[i];
            var_low_ = slice->var_low() + low * base_width;
            var_high_ = slice->var_low() + (high + 1) * base_width - 1;
        }
    }
}

std::string VarSlice::to_string() const {
    auto const &parent_name = parent_var->to_string();
    if (high == low) {
        if (high == 0 && parent_var->width() == 1) {
            return parent_name;
        }
        return ::format("{0}[{1}]", parent_name, high);
    } else {
        return ::format("{0}[{1}:{2}]", parent_name, high, low);
    }
}

const Var *VarSlice::get_var_root_parent() const {
    Var *parent = parent_var;
    while (parent->type() == VarType::Slice) {
        parent = parent->as<VarSlice>()->parent_var;
    }
    return parent;
}

Var *VarSlice::get_var_root_parent() {
    Var *parent = parent_var;
    while (parent->type() == VarType::Slice) {
        parent = parent->as<VarSlice>()->parent_var;
    }
    return parent;
}

std::vector<std::pair<uint32_t, uint32_t>> VarSlice::get_slice_index() const {
    std::vector<std::pair<uint32_t, uint32_t>> result = parent_var->get_slice_index();
    result.emplace_back(std::make_pair(high, low));
    return result;
}

PackedSlice &VarSlice::operator[](const std::string &member_name) {
    auto const *root = get_var_root_parent();
    if (!root->is_packed() || width() != var_width())
        throw UserException(::format("Unable to access {0}.{1}", to_string(), member_name));
    auto p = std::make_shared<PackedSlice>(this, true);
    slices_.emplace_back(p);
    return p->slice_member(member_name);
}

VarVarSlice::VarVarSlice(kratos::Var *parent, kratos::Var *slice)
    : VarSlice(parent, 0, 0), sliced_var_(slice) {
    // check the size or width
    // we need to re-compute var_high, var_low, width, and other stuff by ourselves here
    // there is an issue about the var_high and var_low; the problem will only show up during
    // the connectivity check
    // TODO: fix this
    uint32_t required_width;
    if (parent->size().size() == 1 && parent->size().front() == 1 && !parent->explicit_array()) {
        // slice through the 1D array
        // so the width will be 1
        var_width_ = 1;
        size_ = {1};
        // potentially cover all the bits
        var_high_ = parent->width() - 1;
        var_low_ = 0;
        required_width = clog2(parent->width());
    } else {
        var_width_ = parent->var_width();
        is_packed_ = parent->is_packed();
        // peel one layer
        if (parent->size().size() > 1)
            size_ = std::vector<uint32_t>(parent->size().begin() + 1, parent->size().end());
        else
            size_ = {1};
        var_high_ = parent->var_high();
        var_low_ = parent->var_low();
        // we need to compute the clog2 here
        required_width = clog2(parent->size().front());
    }
    if (required_width < sliced_var_->width()) {
        // may need to demote the variable if it's a var cast
        bool has_error = true;
        if (IterVar::has_iter_var(sliced_var_)) {
            if (IterVar::safe_to_resize(sliced_var_, required_width, false)) {
                IterVar::fix_width(sliced_var_, required_width);
                has_error = false;
            }
        }
        if (has_error || required_width != sliced_var_->width()) {
            // error message copied from verilator
            IterVar::safe_to_resize(sliced_var_, required_width, false);
            throw VarException(
                ::format("Bit extraction of array[{0}:0] requires {1} bit index, not {2} bits.",
                         parent->size().front() - 1, required_width, sliced_var_->width()),
                {parent, slice});
        }
    }
}

void VarVarSlice::add_sink(const std::shared_ptr<AssignStmt> &stmt) {
    VarSlice::add_sink(stmt);
    sliced_var_->add_sink(stmt);
}

void VarVarSlice::add_source(const std::shared_ptr<AssignStmt> &stmt) {
    VarSlice::add_source(stmt);
    sliced_var_->add_sink(stmt);
}

void VarVarSlice::remove_sink(const std::shared_ptr<AssignStmt> &stmt) {
    VarSlice::remove_sink(stmt);
    sliced_var_->remove_sink(stmt);
}

void VarVarSlice::remove_source(const std::shared_ptr<AssignStmt> &stmt) {
    VarSlice::remove_source(stmt);
    sliced_var_->remove_source(stmt);
}

std::string VarVarSlice::to_string() const {
    return ::format("{0}[{1}]", parent_var->to_string(), sliced_var_->to_string());
}

Expr::Expr(ExprOp op, Var *left, Var *right)
    : Var(left->generator(), "", left->var_width(), left->size(), left->is_signed(),
          VarType::Expression),
      op(op),
      left(left),
      right(right) {
    assert(left->ir_node_kind() == IRNodeKind::VarKind);
    if (right != nullptr && left->width() != right->width()) {
        // see if we can resize
        if (IterVar::safe_to_resize(left, right->width(), right->is_signed()) &&
            right->type() != VarType::ConstValue) {
            IterVar::fix_width(left, right->width());
            this->left = left;
        } else if (IterVar::safe_to_resize(right, left->width(), left->is_signed())) {
            IterVar::fix_width(right, left->width());
            this->right = right;
        }
        if (left->width() != right->width())
            throw VarException(
                ::format("left ({0}) width ({1}) doesn't match with right ({2}) width ({3})",
                         left->to_string(), left->width(), right->to_string(), right->width()),
                {left, right});
    }

    // if it's a predicate/relational op, the width is one
    if (is_relational_op(op) || is_reduction_op(op))
        var_width_ = 1;
    else
        var_width_ = left->var_width();

    if (right != nullptr)
        is_signed_ = left->is_signed() & right->is_signed();
    else
        is_signed_ = left->is_signed();
    type_ = VarType::Expression;
    set_parent();

    // both of them has to be packed array
    auto const &left_size = left->size();
    if (right != nullptr && left->is_packed() != right->is_packed() &&
        (left_size.size() > 1 || left_size.front() > 1))
        throw VarException(::format("left is packed ({0}) but right is ({1})", left->is_packed(),
                                    right->is_packed()),
                           {left, right});
    is_packed_ = left->is_packed();
}

Expr::Expr(Var *left, Var *right)
    : Var(left->generator(), "", left->var_width(), left->size(), left->is_signed(),
          VarType::Expression),
      op(ExprOp::Add),
      left(left),
      right(right) {
    type_ = VarType::Expression;
    size_ = std::vector<uint32_t>(left->size().begin(), left->size().end());
    set_parent();
}

uint32_t Expr::width() const {
    if (is_relational_op(op) || is_reduction_op(op)) return 1;
    auto left_width = left->width();
    if (right) {
        auto right_width = right->width();
        // LCOV_EXCL_START
        if (left_width != right_width)
            throw VarException("Unable to resolve expression width", {left, right});
        // LCOV_EXCL_STOP
        return left_width;
    }
    return left_width;
}

void Expr::set_parent() {
    // compute the right parent for the expr
    // it can only go up
    if (!right) {
        generator_ = left->generator();
    } else {
        auto *left_gen = left->generator();
        auto *right_gen = right->generator();
        if (left_gen == Const::const_gen()) {
            generator_ = right_gen;
        } else if (right_gen == Const::const_gen() || !right_gen) {
            generator_ = left_gen;
        } else if (left_gen == right_gen) {
            generator_ = left->generator();
        } else {
            // choose the higher/lower one based on the var type
            if (left_gen == right_gen->parent() && right->type() == VarType::PortIO) {
                generator_ = left_gen;
            } else if (left_gen->parent() == right_gen->parent() &&
                       left->type() == VarType::PortIO && right->type() == VarType::PortIO) {
                generator_ = dynamic_cast<Generator *>(left_gen->parent());
            } else {
                generator_ = right_gen;
            }
        }
    }
}

Var::Var(Generator *module, const std::string &name, uint32_t var_width, uint32_t size,
         bool is_signed)
    : Var(module, name, var_width, size, is_signed, VarType::Base) {}

Var::Var(Generator *module, const std::string &name, uint32_t var_width,
         const std::vector<uint32_t> &size, bool is_signed)
    : Var(module, name, var_width, size, is_signed, VarType::Base) {}

Var::Var(Generator *module, const std::string &name, uint32_t var_width, uint32_t size,
         bool is_signed, VarType type)
    : Var(module, name, var_width, std::vector<uint32_t>{size}, is_signed, type) {}

Var::Var(kratos::Generator *m, const std::string &name, uint32_t var_width,
         std::vector<uint32_t> size, bool is_signed, kratos::VarType type)
    : IRNode(IRNodeKind::VarKind),
      name(name),
      var_width_(var_width),
      size_(std::move(size)),
      is_signed_(is_signed),
      type_(type),
      generator_(m) {
    // only constant allows to be null generator
    if (m == nullptr && type != VarType::ConstValue && type != VarType::Iter)
        throw UserException(::format("module is null for {0}", name));
    if (!is_valid_variable_name(name))
        throw UserException(::format("{0} is a SystemVerilog keyword", name));
    if (var_width == 0) throw UserException(::format("variable {0} cannot have size 0", name));
}

IRNode *Var::parent() { return generator(); }
IRNode *VarSlice::parent() { return parent_var; }

std::shared_ptr<AssignStmt> Var::assign(const std::shared_ptr<Var> &var) {
    return assign(var, AssignmentType::Undefined);
}

std::shared_ptr<AssignStmt> Var::assign(Var &var) {
    return assign(var.shared_from_this(), AssignmentType::Undefined);
}

std::shared_ptr<AssignStmt> Var::assign(const std::shared_ptr<Var> &var, AssignmentType type) {
    return assign_(var, type);
}

std::shared_ptr<AssignStmt> Var::assign_(const std::shared_ptr<Var> &var, AssignmentType type) {
    // if it's a constant or expression, it can't be assigned to
    if (type_ == VarType::ConstValue)
        throw VarException(::format("Cannot assign {0} to a const {1}", var->to_string(), name),
                           {this, var.get()});
    else if (type_ == VarType::Expression)
        throw VarException(::format("Cannot assign {0} to an expression", var->to_string(), name),
                           {this, var.get()});
    auto stmt = ::make_shared<AssignStmt>(shared_from_this(), var, type);

    return stmt;
}

void Var::unassign(const std::shared_ptr<AssignStmt> &stmt) {
    // we need to take care of the slices
    stmt->right()->sinks_.erase(stmt);
    sources_.erase(stmt);
    // erase from parent if any
    // TODO: fix this will proper parent
    generator()->remove_stmt(stmt);
}

Const::Const(Generator *generator, int64_t value, uint32_t width, bool is_signed)
    : Var(generator, std::to_string(value), width, 1, is_signed, VarType::ConstValue), value_() {
    // need to deal with the signed value
    auto is_legal = Const::is_legal(value, width, is_signed);
    if (is_legal == ConstantLegal::Small) {
        uint64_t temp = (~0ull) << (width - 1);
        int64_t min = 0;
        std::memcpy(&min, &temp, sizeof(min));
        throw UserException(::format("{0} is smaller than the minimum value ({1}) given width {2}",
                                     value, min, width));
    } else if (is_legal == ConstantLegal::Big) {
        uint64_t max = (1ull << width) - 1;
        uint64_t unsigned_value;
        std::memcpy(&unsigned_value, &value, sizeof(unsigned_value));
        throw UserException(::format("{0} is larger than the maximum value ({1}) given width {2}",
                                     value, max, width));
    }
    value_ = value;
}

Const::ConstantLegal Const::is_legal(int64_t value, uint32_t width, bool is_signed) {
    if (is_signed) {
        // compute the -max value
        uint64_t temp = (~0ull) << (width - 1);
        int64_t min = 0;
        std::memcpy(&min, &temp, sizeof(min));
        if (value < min) return Const::ConstantLegal::Small;
        temp = (1ull << (width - 1)) - 1;
        int64_t max;
        std::memcpy(&max, &temp, sizeof(max));
        if (value > max) return Const::ConstantLegal::Big;
    } else {
        uint64_t max = (1ull << width) - 1;
        uint64_t unsigned_value;
        std::memcpy(&unsigned_value, &value, sizeof(unsigned_value));
        if (unsigned_value > max) return Const::ConstantLegal::Big;
    }
    return Const::ConstantLegal::Legal;
}

Const::Const(int64_t value, uint32_t width, bool is_signed)
    : Const(nullptr, value, width, is_signed) {
    if (!const_generator_) const_generator_ = std::make_shared<Generator>(nullptr, "");
    generator_ = const_generator_.get();
}

Const &Const::constant(int64_t value, uint32_t width, bool is_signed) {
    auto p = std::make_shared<Const>(value, width, is_signed);
    consts_.emplace(p);
    return *p;
}

void Const::set_is_packed(bool value) {
    if (!value) throw UserException("Unable to set const unpacked");
}

std::unordered_set<std::shared_ptr<Const>> Const::consts_ = {};
std::shared_ptr<Generator> Const::const_generator_ = nullptr;

VarCasted::VarCasted(Var *parent, VarCastType cast_type)
    : Var(parent->generator(), "", parent->width(), parent->size(), false, parent->type()),
      parent_var_(parent),
      cast_type_(cast_type) {
    type_ = VarType::BaseCasted;
    if (cast_type_ == VarCastType::Signed) {
        is_signed_ = true;
    } else if (cast_type_ == VarCastType::Unsigned) {
        is_signed_ = false;
    } else if (cast_type_ == VarCastType::AsyncReset || cast_type_ == VarCastType::Clock) {
        if (parent->size().size() != 1 || parent->size().front() != 1) {
            throw VarException(::format("Can only cast bit width 1 to "
                                        "Clock or AsyncReset. {0} is {1}",
                                        parent->to_string(), parent->size().front()),
                               {parent});
        }
    }
}

std::shared_ptr<AssignStmt> VarCasted::assign_(const std::shared_ptr<Var> &, AssignmentType) {
    throw VarException(::format("{0} is not allowed to be a sink", to_string()), {this});
}

std::string VarCasted::to_string() const {
    if (cast_type_ == VarCastType::Signed) {
        return ::format("signed'({0})", parent_var_->to_string());
    } else if (cast_type_ == VarCastType::Unsigned) {
        return ::format("unsigned'({0})", parent_var_->to_string());
    } else if (cast_type_ == VarCastType::Enum) {
        if (!enum_type_) {
            throw UserException(
                ::format("Variable {0} is casted as a enum without "
                         "enum type information",
                         parent_var_->to_string()));
        }
        auto const &enum_name = enum_type_->name;
        return ::format("{0}'({1})", enum_name, parent_var_->to_string());
    } else if (cast_type_ == VarCastType::Resize) {
        return ::format("{0}'({1})", target_width_, parent_var_->to_string());
    } else {
        return parent_var_->to_string();
    }
}

void VarCasted::set_target_width(uint32_t width) {
    // override the current width
    if (parent_var_->size().size() > 1 && parent_var_->size().front() != 1) {
        throw UserException("Width casting for array not supported");
    }
    if (cast_type_ == VarCastType::Resize) {
        target_width_ = width;
        var_width_ = width;
    }
}

void VarCasted::add_sink(const std::shared_ptr<AssignStmt> &stmt) { parent_var_->add_sink(stmt); }

std::shared_ptr<Var> Var::cast(VarCastType cast_type) {
    if (cast_type == VarCastType::Signed && is_signed_) {
        return shared_from_this();
    } else {
        // optimize memory for speed
        for (auto const &casted : casted_) {
            if (casted->cast_type() == cast_type && cast_type != VarCastType::Resize) {
                return casted;
            }
        }
        auto v = std::make_shared<VarCasted>(this, cast_type);
        casted_.emplace(v);
        return v;
    }
}

void Const::set_value(int64_t new_value) {
    if (Const::is_legal(new_value, width(), is_signed()) != Const::ConstantLegal::Legal) {
        throw VarException(
            ::format("Unable to set const to {0} with width {1}", new_value, width()), {this});
    }
    value_ = new_value;
}

void Const::set_width(uint32_t target_width) {
    if (Const::is_legal(value_, target_width, is_signed()) != Const::ConstantLegal::Legal) {
        throw VarException(::format("Unable to set const {0} to width {1}", value_, target_width),
                           {this});
    }
    var_width_ = target_width;
}

void Const::add_source(const std::shared_ptr<AssignStmt> &) {
    throw VarException(::format("const {0} is not allowed to be driven by a net", to_string()),
                       {this});
}

void Const::add_sink(const std::shared_ptr<AssignStmt> &stmt) {
    auto left = stmt->left();
    // if it's a port, we change the constant's generator to that of port
    auto generator = left->generator();
    if (!generator)
        throw StmtException(::format("Unable to find left hand side generator"), {stmt.get()});
    auto parent = generator->parent();
    if (parent && parent->ir_node_kind() == GeneratorKind) {
        auto gen = dynamic_cast<Generator *>(parent);
        this->generator_ = gen;
    }
}

Param::Param(Generator *m, std::string name, uint32_t width, bool is_signed)
    : Const(m, 1, width, is_signed), parameter_name_(std::move(name)) {
    // override the type value
    type_ = VarType::Parameter;
}

Param::Param(Generator *m, std::string name)
    : Const(m, 0, 1, false), parameter_name_(std::move(name)), param_type_(ParamType::RawType) {
    // override the type value
    type_ = VarType::Parameter;
}

Param::Param(Generator *m, std::string name, Enum *enum_def)
    : Const(m, 0, enum_def->width(), false),
      parameter_name_(std::move(name)),
      param_type_(ParamType::Enum),
      enum_def_(enum_def) {
    type_ = VarType::Parameter;
}

void Param::set_value(int64_t new_value) {
    if (new_value <= 0 && !param_vars_width_.empty()) {
        throw VarException(
            ::format(
                "{0} is used for parametrizing variable width, thus cannot be non-positive ({1})",
                to_string(), new_value),
            {this});
    }
    Const::set_value(new_value);
    has_value_ = true;

    // change the width of parametrized variables
    for (const auto &var : param_vars_width_) {
        var->var_width() = new_value;
    }
    // change the size as well
    for (const auto &[var, index, expr] : param_vars_size_) {
        var->set_size_param(index, expr);
    }

    // change the entire chain
    for (const auto &param : param_params_) {
        param->set_value(new_value);
    }
}

std::string Param::value_str() const {
    if (param_type_ == ParamType::Integral) {
        return Const::to_string();
    } else if (param_type_ == ParamType::Parameter) {
        const auto *p = parent_param();
        return p->to_string();
    } else {
        // raw type
        return name;
    }
}

void Param::add_param_size_var(Var *var, uint32_t index, Var *expr) {
    param_vars_size_.emplace(std::make_tuple(var, index, expr));
}

void Param::set_value(const std::shared_ptr<Param> &param) {
    param->param_params_.emplace(this);
    parent_param_ = param.get();
    param_type_ = ParamType::Parameter;

    // update the values
    set_value(param->value());
}

void VarConcat::add_source(const std::shared_ptr<kratos::AssignStmt> &stmt) {
    for (auto &var : vars_) {
        var->add_source(stmt);
    }
}

void VarConcat::add_sink(const std::shared_ptr<kratos::AssignStmt> &stmt) {
    for (auto &var : vars_) {
        var->add_sink(stmt);
    }
}

std::string VarConcat::to_string() const {
    std::vector<std::string> var_names;
    for (const auto &ptr : vars_) {
        var_names.emplace_back(ptr->to_string());
    }
    auto content = string::join(var_names.begin(), var_names.end(), ", ");
    return ::format("{{{0}}}", content);
}

std::string VarConcat::handle_name(bool ignore_top) const {
    std::vector<std::string> var_names;
    for (const auto &ptr : vars_) {
        var_names.emplace_back(ptr->handle_name(ignore_top));
    }
    auto content = string::join(var_names.begin(), var_names.end(), ", ");
    return ::format("{{{0}}}", content);
}

std::string VarConcat::handle_name(kratos::Generator *scope) const {
    std::vector<std::string> var_names;
    for (const auto &ptr : vars_) {
        var_names.emplace_back(ptr->handle_name(scope));
    }
    auto content = string::join(var_names.begin(), var_names.end(), ", ");
    return ::format("{{{0}}}", content);
}

VarConcat::VarConcat(const std::shared_ptr<VarConcat> &first, const std::shared_ptr<Var> &second)
    : Expr(first.get(), second.get()) {
    if (first->is_signed_ != second->is_signed())
        throw VarException(
            ::format("{0} is signed but {1} is not", first->to_string(), second->to_string()),
            {first.get(), second.get()});
    vars_ = std::vector<Var *>(first->vars_.begin(), first->vars_.end());
    vars_.emplace_back(second.get());
    var_width_ = first->width() + second->width();
    op = ExprOp::Concat;
}

VarConcat::VarConcat(const std::shared_ptr<Var> &first, const std::shared_ptr<Var> &second)
    : Expr(first.get(), second.get()) {
    if (first->is_signed() != second->is_signed())
        throw VarException(
            ::format("{0} is signed but {1} is not", first->to_string(), second->to_string()),
            {first.get(), second.get()});
    vars_ = {first.get(), second.get()};
    var_width_ = first->width() + second->width();
    op = ExprOp::Concat;
}

VarConcat &VarConcat::concat(kratos::Var &var) {
    auto result = std::make_shared<VarConcat>(as<VarConcat>(), var.shared_from_this());
    // add it to the first one
    vars_[0]->add_concat_var(result);
    return *result;
}

void VarConcat::replace_var(const std::shared_ptr<Var> &target, const std::shared_ptr<Var> &item) {
    auto pos = std::find(vars_.begin(), vars_.end(), target.get());
    if (pos != vars_.end()) {
        *pos = item.get();
    }
}

VarExtend::VarExtend(const std::shared_ptr<Var> &var, uint32_t width)
    : Expr(ExprOp::Extend, var.get(), nullptr), parent_(var.get()) {
    if (width < parent_->width()) {
        throw VarException(::format("Cannot extend {0} (width={1}) to {2}", parent_->to_string(),
                                    parent_->width(), width),
                           {parent_});
    }
    var_width_ = width;
    is_signed_ = parent_->is_signed();
    if (parent_->size().size() > 1 || parent_->size().front() > 1 ||
        (parent_->is_packed() && parent_->type() != VarType::ConstValue)) {
        throw VarException(::format("Cannot extend an array ({0})", parent_->to_string()),
                           {parent_});
    }
}

void VarExtend::add_source(const std::shared_ptr<AssignStmt> &) {
    throw StmtException(
        ::format("Cannot add source to an extended variable ({0})", parent_->to_string()),
        {parent_});
}

void VarExtend::add_sink(const std::shared_ptr<AssignStmt> &stmt) { parent_->add_sink(stmt); }

void VarExtend::replace_var(const std::shared_ptr<Var> &target, const std::shared_ptr<Var> &item) {
    if (target.get() == parent_) {
        parent_ = item.get();
    }
}

std::string VarExtend::to_string() const {
    return ::format("{0}'({1})", width(), parent_->to_string());
}

std::string Const::to_string() const {
    if (is_signed_ && value_ < 0) {
        return ::format("-{0}\'h{1:X}", width(), -value_);
    } else {
        return ::format("{0}\'h{1:X}", width(), value_);
    }
}

std::shared_ptr<AssignStmt> Var::assign(Var &var, AssignmentType type) {
    // need to find the pointer
    auto var_ptr = var.shared_from_this();
    return assign(var_ptr, type);
}

std::string inline expr_to_string(const Expr *expr, bool is_top, bool use_handle,
                                  bool ignore_top = false, Generator *scope = nullptr) {
    // overloaded to_string methods?
    if (is_expand_op(expr->op))
        return use_handle ? expr->handle_name(ignore_top)
               : scope    ? expr->handle_name(scope)
                          : expr->to_string();
    if (expr->op == ExprOp::Conditional)
        return ::format("({0})", use_handle ? expr->handle_name(ignore_top)
                                 : scope    ? expr->handle_name(scope)
                                            : expr->to_string());

    auto *left = expr->left;
    auto *right = expr->right;

    auto left_str = left->type() == VarType::Expression
                        ? expr_to_string(left->as<Expr>().get(), expr->op == left->as<Expr>()->op,
                                         use_handle, ignore_top, scope)
                        : (use_handle ? left->handle_name(ignore_top)
                           : scope    ? left->handle_name(scope)
                                      : left->to_string());

    if (right != nullptr) {
        auto right_str =
            right->type() == VarType::Expression
                ? expr_to_string(right->as<Expr>().get(), expr->op == right->as<Expr>()->op,
                                 use_handle, ignore_top, scope)
                : (use_handle ? right->handle_name(ignore_top)
                   : scope    ? right->handle_name(scope)
                              : right->to_string());
        if (is_top)
            return ::format("{0} {1} {2}", left_str, ExprOpStr(expr->op), right_str);
        else
            return ::format("({0} {1} {2})", left_str, ExprOpStr(expr->op), right_str);
    } else {
        if (is_top)
            return ::format("{0}{1}", ExprOpStr(expr->op), left_str);
        else
            return ::format("({0}{1})", ExprOpStr(expr->op), left_str);
    }
}

std::string Expr::to_string() const { return expr_to_string(this, true, false); }

std::string Expr::handle_name(bool ignore_top) const {
    return expr_to_string(this, true, true, ignore_top);
}

std::string Expr::handle_name(kratos::Generator *scope) const {
    return expr_to_string(this, true, false, scope);
}

IRNode *Expr::get_child(uint64_t index) {
    if (index == 0)
        return left;
    else if (index == 1)
        return right ? right : nullptr;
    else
        return nullptr;
}

void set_slice_var_parent(Var *&var, Var *target, Var *new_var, bool check_target) {
    std::shared_ptr<VarSlice> slice;
    Var *parent_var = var;
    std::vector<std::shared_ptr<VarSlice>> slices;
    while (parent_var->type() == VarType::Slice) {
        // this is for nested slicing
        slice = parent_var->as<VarSlice>();
        slices.emplace_back(slice);
        parent_var = slice->parent_var;
    }
    if (parent_var != target) {
        if (check_target)
            throw InternalException("Target not found");
        else
            return;
    }
    if (!slice) throw InternalException("Slice cannot be null");

    auto new_var_ptr = new_var->as<Var>();
    std::reverse(slices.begin(), slices.end());
    for (auto const &s : slices) {
        new_var_ptr = s->slice_var(new_var_ptr);
    }
    var = new_var_ptr.get();
}

void change_var_expr(const std::shared_ptr<Expr> &expr, Var *target, Var *new_var) {
    if (!new_var || !target) throw InternalException("Variable is NULL");
    if (expr->left->type() == VarType::Expression) {
        change_var_expr(expr->left->as<Expr>(), target, new_var);
    }
    if (expr->right && expr->right->type() == VarType::Expression) {
        change_var_expr(expr->right->as<Expr>(), target, new_var);
    }

    if (expr->left == target) {
        expr->left = new_var;
        expr->left->move_linked_to(new_var);
    }
    if (expr->right && expr->right == target) {
        expr->right = new_var;
        expr->right->move_linked_to(new_var);
    }

    // need to change the parent as well
    if (expr->left->type() == VarType::Slice) {
        set_slice_var_parent(expr->left, target, new_var, false);
    }
    if (expr->right && expr->right->type() == VarType::Slice) {
        set_slice_var_parent(expr->right, target, new_var, false);
    }
    // we did some tricks on the concatenation, need to update them there
    if (expr->op == ExprOp::Concat) {
        auto concat = expr->as<VarConcat>();
        concat->replace_var(target->shared_from_this(), new_var->shared_from_this());
    }
}

void change_cast_parent(const std::shared_ptr<VarCasted> &var, Var *target, Var *new_var);

void change_var_parent(Var *&var, Var *target, Var *new_var) {
    if (var->type() == VarType::Slice) {
        set_slice_var_parent(var, target, new_var, true);
    } else if (var->type() == VarType::Expression) {
        auto expr = var->as<Expr>();
        change_var_expr(expr, target, new_var);
    } else if (var->type() == VarType::BaseCasted) {
        change_cast_parent(var->as<VarCasted>(), target, new_var);
    }
}

void change_cast_parent(const std::shared_ptr<VarCasted> &var, Var *target, Var *new_var) {
    auto &p = var->parent_var();
    if (p == target) {
        p = new_var;
    } else {
        change_var_parent(p, target, new_var);
    }
}

void stmt_set_right(AssignStmt *stmt, Var *target, Var *new_var) {
    auto &right = stmt->right();
    if (right->type() == VarType::Base || right->type() == VarType::PortIO ||
        right->type() == VarType::ConstValue) {
        if (right == target) {
            stmt->set_right(new_var->shared_from_this());
            right->move_linked_to(new_var);
        } else {
            throw InternalException("Target not found");
        }
    } else if (right->type() == VarType::Slice) {
        set_slice_var_parent(right, target, new_var, true);
    } else if (right->type() == VarType::Expression) {
        change_var_expr(stmt->right()->as<Expr>(), target, new_var);
    } else {
        change_var_parent(right, target, new_var);
    }
}

void stmt_set_left(AssignStmt *stmt, Var *target, Var *new_var) {
    auto &left = stmt->left();
    if (left->type() == VarType::Base || left->type() == VarType::PortIO ||
        left->type() == VarType::ConstValue) {
        if (left == target) {
            stmt->set_left(new_var->shared_from_this());
            left->move_linked_to(new_var);
        } else {
            throw InternalException("Target not found");
        }
    } else {
        change_var_parent(left, target, new_var);
    }
}

void Var::move_src_to(Var *var, Var *new_var, Generator *parent, bool keep_connection) {
    // only base and port vars are allowed
    if (var->type_ == VarType::Expression || var->type_ == VarType::ConstValue)
        throw VarException("Only base or port variables are allowed.", {var, new_var});

    for (auto &stmt : var->sources()) {
        if (stmt->generator_parent() != parent) continue;
        stmt_set_left(stmt.get(), var, new_var);
        if (parent->debug) {
            stmt->fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
        }
        new_var->add_source(stmt);
        // pick a source parameter, if any
        if (stmt->right()->parametrized() && !new_var->parametrized()) {
            new_var->set_width_param(stmt->right()->param());
        }
    }
    // now clear the sources
    var->clear_sources(false);

    if (keep_connection) {
        // create an assignment and add it to the parent
        auto stmt = var->assign(new_var->shared_from_this());
        if (parent->debug) {
            stmt->fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
        }
        parent->add_stmt(stmt);
    }
}

void Var::move_sink_to(Var *var, Var *new_var, Generator *parent, bool keep_connection) {
    // only base and port vars are allowed
    if (var->type_ == VarType::Expression || var->type_ == VarType::ConstValue)
        throw VarException("Only base or port variables are allowed.", {var, new_var});

    for (auto &stmt : var->sinks()) {
        if (stmt->generator_parent() != parent) {
            continue;
        }
        stmt_set_right(stmt.get(), var, new_var);
        if (parent->debug) {
            stmt->fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
        }
        new_var->add_sink(stmt);
        // pick a source parameter, if any
        if (stmt->left()->parametrized() && !new_var->parametrized()) {
            new_var->set_width_param(stmt->left()->param());
        }
    }
    // now clear the sinks
    var->clear_sinks(false);

    if (keep_connection) {
        // create an assignment and add it to the parent
        auto stmt = new_var->assign(var->shared_from_this());
        if (parent->debug) {
            stmt->fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
        }
        parent->add_stmt(stmt);
    }
}

void Var::move_linked_to(kratos::Var *new_var) {
    if (this == new_var->get_var_root_parent()) return;
    // this one doesn't do much checking
    // user code code should check instead
    if (new_var->width() != width()) {
        throw VarException(::format("Try to move linked variable to a variable that "
                                    "doesn't match width. Need {0}, got {1}",
                                    width(), new_var->width()),
                           {this, new_var});
    }
    if (new_var->is_signed() != is_signed()) {
        throw VarException(::format("Try to move linked variable to a variable that "
                                    "doesn't match sign. Need {0}, got {1}",
                                    is_signed() ? "signed" : "unsigned",
                                    new_var->is_signed() ? "signed" : "unsigned"),
                           {this, new_var});
    }
    // move all references held in var to the new var
    // and change the parents
    for (auto &slice : slices_) {
        slice->set_parent(new_var);
    }
    new_var->slices_ = std::vector(slices_.begin(), slices_.end());
    slices_.clear();

    // change concat'ed vars
    // we use overloaded ones
    for (auto &concat : concat_vars_) {
        concat->move_linked_to(new_var);
        concat->replace_var(shared_from_this(), new_var->shared_from_this());
    }
    new_var->concat_vars_ =
        std::unordered_set<std::shared_ptr<VarConcat>>(concat_vars_.begin(), concat_vars_.end());
    concat_vars_.clear();

    // casted
    for (auto &var : casted_) {
        var->set_parent(new_var->get_var_root_parent());
        new_var->get_var_root_parent()->casted_.emplace(var);
    }
    casted_.clear();
}

void Var::clear_sources(bool remove_parent) {  // NOLINT
    if (remove_parent) {
        for (auto &stmt : sources_) {
            stmt->remove_from_parent();
        }
    }

    sources_.clear();
}

void Var::clear_sinks(bool remove_parent) {  // NOLINT
    if (remove_parent) {
        for (auto &stmt : sinks_) {
            if (stmt->parent()) stmt->remove_from_parent();
        }
    }

    sinks_.clear();
}

void Expr::add_sink(const std::shared_ptr<AssignStmt> &stmt) {
    left->add_sink(stmt);
    if (right) right->add_sink(stmt);
}

void VarSlice::add_sink(const std::shared_ptr<AssignStmt> &stmt) {
    Var *parent = parent_var;
    parent->add_sink(stmt);
}

void VarSlice::add_source(const std::shared_ptr<AssignStmt> &stmt) {
    Var *parent = parent_var;
    parent->add_source(stmt);
}

void VarSlice::remove_source(const std::shared_ptr<AssignStmt> &stmt) {
    Var *parent = parent_var;
    parent->remove_source(stmt);
}

void VarSlice::remove_sink(const std::shared_ptr<AssignStmt> &stmt) {
    Var *parent = parent_var;
    parent->remove_source(stmt);
}

ConditionalExpr::ConditionalExpr(const std::shared_ptr<Var> &condition,
                                 const std::shared_ptr<Var> &left,
                                 const std::shared_ptr<Var> &right)
    : Expr(ExprOp::Conditional, left.get(), right.get()), condition(condition.get()) {
    if (condition->width() != 1)
        throw VarException("Ternary operator's condition has to be a binary value",
                           {condition.get()});
}

IRNode *ConditionalExpr::get_child(uint64_t index) {
    if (index == 0)
        return condition;
    else if (index == 1)
        return left;
    else if (index == 2)
        return right;
    else
        return nullptr;
}

void ConditionalExpr::add_sink(const std::shared_ptr<AssignStmt> &stmt) {
    condition->add_sink(stmt);
    left->add_sink(stmt);
    right->add_sink(stmt);
}

std::string ConditionalExpr::to_string() const {
    std::string cond_str = condition->type() == VarType::Expression
                               ? ::format("({0})", condition->to_string())
                               : condition->to_string();
    return ::format("{0} ? {1}: {2}", cond_str, left->to_string(), right->to_string());
}

std::string ConditionalExpr::handle_name(bool ignore_top) const {
    return ::format("{0} ? {1}: {2}", condition->handle_name(ignore_top),
                    left->handle_name(ignore_top), right->handle_name(ignore_top));
}

std::string ConditionalExpr::handle_name(kratos::Generator *scope) const {
    return ::format("{0} ? {1}: {2}", condition->handle_name(scope), left->handle_name(scope),
                    right->handle_name(scope));
}

PackedStruct::PackedStruct(std::string struct_name,
                           std::vector<std::tuple<std::string, uint32_t, bool>> attributes)
    : struct_name(std::move(struct_name)), attributes(std::move(attributes)) {}

PackedStruct::PackedStruct(std::string struct_name,
                           const std::vector<std::tuple<std::string, uint32_t>> &attributes)
    : struct_name(std::move(struct_name)) {
    for (auto const &[name, size] : attributes) {
        this->attributes.emplace_back(std::make_tuple(name, size, false));
    }
}

PackedSlice::PackedSlice(PortPackedStruct *parent, const std::string &member_name)
    : VarSlice(parent, 0, 0), member_name_(member_name) {
    auto const &struct_ = parent->packed_struct();
    set_up(struct_, member_name);
}

PackedSlice::PackedSlice(kratos::VarPackedStruct *parent, const std::string &member_name)
    : VarSlice(parent, 0, 0), member_name_(member_name) {
    auto const &struct_ = parent->packed_struct();
    set_up(struct_, member_name);
}

PackedSlice::PackedSlice(VarSlice *slice, bool is_root)
    : VarSlice(slice, 0, 0), is_root_(is_root) {}

void PackedSlice::set_up(const kratos::PackedStruct &struct_, const std::string &member_name) {
    // compute the high and low
    uint32_t low_ = 0;
    bool found = false;
    for (auto const &[name, width, is_signed] : struct_.attributes) {
        if (name == member_name) {
            found = true;
            high = width + low_ - 1;
            low = low_;
            is_signed_ = is_signed;
            var_high_ = high;
            var_low_ = low;
            break;
        } else {
            low_ += width;
        }
    }

    if (!found) {
        throw InternalException(
            ::format("{0} does not exist in {1}", member_name, struct_.struct_name));
    }
}

shared_ptr<Var> PackedSlice::slice_var(std::shared_ptr<Var> var) {
    if (is_root_) return var;
    if (var->type() == VarType::PortIO) {
        auto v = var->as<PortPackedStruct>();
        return v->operator[](member_name_).shared_from_this();
    } else {
        auto v = var->as<VarPackedStruct>();
        return v->operator[](member_name_).shared_from_this();
    }
}

PackedSlice &PackedSlice::slice_member(const std::string &member_name) {
    if (!is_root_) throw UserException("Only struct array can slice member at the end");
    auto *root = get_var_root_parent();
    std::shared_ptr<PackedSlice> p;
    if (root->type() == VarType::PortIO) {
        auto v = root->as<PortPackedStruct>();
        p = ::make_shared<PackedSlice>(this, false);
        p->set_up(v->packed_struct(), member_name);
    } else {
        auto v = root->as<VarPackedStruct>();
        p = ::make_shared<PackedSlice>(this, false);
        p->set_up(v->packed_struct(), member_name);
    }
    p->member_name_ = member_name;
    slices_.emplace_back(p);
    return *p;
}

std::string PackedSlice::to_string() const {
    if (is_root_) {
        return parent_var->to_string();
    } else {
        return ::format("{0}.{1}", parent_var->to_string(), member_name_);
    }
}

PackedSlice &VarPackedStruct::operator[](const std::string &member_name) {
    if (width() != var_width())
        throw UserException(
            ::format("Unable to access member of {0}, which is an array", to_string()));
    auto ptr = std::make_shared<PackedSlice>(this, member_name);
    slices_.emplace_back(ptr);
    return *ptr;
}

VarPackedStruct::VarPackedStruct(Generator *m, const std::string &name, PackedStruct packed_struct_)
    : Var(m, name, 1, 1, false), struct_(std::move(packed_struct_)) {
    compute_width();
}

VarPackedStruct::VarPackedStruct(Generator *m, const std::string &name, PackedStruct packed_struct_,
                                 uint32_t size)
    : Var(m, name, 1, size, false), struct_(std::move(packed_struct_)) {
    compute_width();
}

VarPackedStruct::VarPackedStruct(Generator *m, const std::string &name, PackedStruct packed_struct_,
                                 const std::vector<uint32_t> &size)
    : Var(m, name, 1, size, false), struct_(std::move(packed_struct_)) {
    compute_width();
}

void VarPackedStruct::compute_width() {
    // compute the width
    uint32_t width = 0;
    for (auto const &def : struct_.attributes) {
        width += std::get<1>(def);
    }
    var_width_ = width;
}

std::set<std::string> VarPackedStruct::member_names() const {
    std::set<std::string> result;
    for (auto const &def : struct_.attributes) {
        result.emplace(std::get<0>(def));
    }
    return result;
}

void VarPackedStruct::set_is_packed(bool value) {
    if (!value) throw UserException("Unable to set packed struct unpacked");
}

Enum::Enum(const std::string &name, const std::map<std::string, uint64_t> &values, uint32_t width)
    : name(name), width_(width) {
    if (!is_valid_variable_name(name)) {
        throw UserException(::format("{0} is a SystemVerilog keyword", name));
    }
    for (auto const &[n, value] : values) {
        auto c = std::make_shared<EnumConst>(Const::const_gen(), value, width, this, n);
        this->values.emplace(n, c);
    }
}

std::shared_ptr<EnumConst> Enum::get_enum(const std::string &enum_name) {
    if (values.find(enum_name) == values.end())
        throw UserException(::format("Cannot find {0} in {1}", enum_name, name));
    return values.at(enum_name);
}

void Enum::verify_naming_conflict(const std::map<std::string, std::shared_ptr<Enum>> &enums,
                                  const std::string &name,
                                  const std::map<std::string, uint64_t> &values) {
    if (enums.find(name) != enums.end())
        throw UserException(::format("{0} already exists in scope", name));
    // check name conflicts
    std::set<std::string> names;
    std::set<std::string> used_names;
    for (auto const &iter : values) {
        names.emplace(iter.first);
    }
    // find all enum definition used in the generator
    // name mapping
    std::unordered_map<std::string, Enum *> name_mapping;
    for (auto const &iter : enums) {
        auto const &enum_ = iter.second;
        auto const &values_ = enum_->values;
        for (auto const &iter2 : values_) {
            used_names.emplace(iter2.first);
            name_mapping.emplace(iter2.first, enum_.get());
        }
    }
    // if there is an overlap/intersection
    std::set<std::string> overlap;
    std::set_intersection(names.begin(), names.end(), used_names.begin(), used_names.end(),
                          std::inserter(overlap, overlap.begin()));
    if (!overlap.empty()) {
        // pick a random one, don't care
        auto used_name = *overlap.begin();
        auto const &enum_def = name_mapping.at(used_name);
        throw UserException(::format("{0} has been used in {1}.{0}", used_name, enum_def->name));
    }
}

void Enum::add_debug_info(const std::string &enum_name,
                          const std::pair<std::string, uint32_t> &debug) {
    auto var = values.at(enum_name);
    var->fn_name_ln.emplace_back(debug);
}

EnumConst::EnumConst(kratos::Generator *m, int64_t value, uint32_t width, kratos::Enum *parent,
                     std::string name)
    : Const(m, value, width, false), parent_(parent), name_(std::move(name)) {}

std::string EnumConst::to_string() const {
    if (parent_->values.find(name_) == parent_->values.end()) {
        throw VarException(::format("{0} is not in enum type {1}", name_, parent_->name), {this});
    }
    return name_;
}

IterVar::IterVar(kratos::Generator *m, const std::string &name, int64_t min_value,
                 int64_t max_value, bool signed_)
    : Var(m, name, 32u, 1, signed_, VarType::Iter), min_value_(min_value), max_value_(max_value) {
    // we always use 32
    // by default it is unsigned
}

void extract_iter_var(const Var *var, std::vector<const IterVar *> &iters) {
    if (!var) return;
    if (var->type() == VarType::Iter) {
        iters.emplace_back(reinterpret_cast<const IterVar *>(var));
    } else if (var->type() == VarType::Expression) {
        auto expr = reinterpret_cast<const Expr *>(var);
        extract_iter_var(expr->left, iters);
        extract_iter_var(expr->right, iters);
    }
}

std::optional<int64_t> convert_value(const Var *var,
                                     const std::optional<std::vector<uint64_t>> &values) {
    if (!values) {
        return std::nullopt;
    }
    auto v = &((*values)[0]);
    if (var->is_signed()) {
        auto s_v = reinterpret_cast<const int64_t *>(v);
        return *s_v;
    } else {
        return *v;
    }
}

bool safe_to_resize_(Simulator &sim, const Var *var, uint32_t target_size, bool is_signed,
                     std::queue<const IterVar *> &vars) {
    // notice it's exclusive for max
    if (vars.empty()) {
        const auto *p = var->get_var_root_parent();
        if (p->type() == VarType::Base || p->type() == VarType::PortIO)
            return var->width() <= target_size;
        else
            return true;
    } else {
        // pop one
        auto *t = const_cast<IterVar *>(vars.front());
        vars.pop();
        sim.set_i(t, t->min_value(), false);
        {
            auto v = sim.eval_expr(var);
            auto num = convert_value(var, v);
            if (!num) return false;
            auto result =
                Const::is_legal(*num, target_size, is_signed) == Const::ConstantLegal::Legal;
            if (!result) return false;
        }
        // notice it's exclusive for max
        sim.set_i(t, t->max_value() - 1, false);
        {
            auto v = sim.eval_expr(var);
            auto num = convert_value(var, v);
            if (!num) return false;
            auto result =
                Const::is_legal(*num, target_size, is_signed) == Const::ConstantLegal::Legal;
            if (!result) return false;
        }
        auto r = safe_to_resize_(sim, var, target_size, is_signed, vars);
        // put it back for backtracking
        vars.push(t);
        return r;
    }
}

bool IterVar::safe_to_resize(const Var *var, uint32_t target_size, bool is_signed) {
    std::vector<const IterVar *> iters;
    extract_iter_var(var, iters);
    // brute-force to compute every possible combinations using simulator
    static Simulator sim(nullptr);
    // We did some hacks that, assuming the min and max value is at the boundary
    // maybe use a SMT solver?
    std::queue<const IterVar *> queue;
    for (auto const &v : iters) {
        sim.set_i(v, v->max_value() - 1, false);
        queue.emplace(v);
    }

    auto result = safe_to_resize_(sim, var, target_size, is_signed, queue);

    return result;
}

bool IterVar::has_iter_var(const Var *var) {
    if (!var) return false;
    if (var->type() == VarType::Iter) return true;
    if (var->type() == VarType::Slice) {
        auto slice = reinterpret_cast<const VarSlice *>(var);
        return has_iter_var(slice->get_var_root_parent());
    } else if (var->type() == VarType::Expression) {
        auto expr = reinterpret_cast<const Expr *>(var);
        return has_iter_var(expr->left) || has_iter_var(expr->right);
    }
    return false;
}

void IterVar::fix_width(Var *&var, uint32_t target_width) {
    if (var && var->type() == VarType::Iter) {
        auto *iter = reinterpret_cast<IterVar *>(var);
        auto casted = iter->cast(VarCastType::Resize)->as<VarCasted>();
        casted->set_target_width(target_width);
        var = casted.get();
    } else if (var && var->type() == VarType::ConstValue) {
        auto *c = reinterpret_cast<Const *>(var);
        c->set_width(target_width);
    } else if (var && var->type() == VarType::Expression) {
        auto *expr = reinterpret_cast<Expr *>(var);
        fix_width(expr->left, target_width);
        fix_width(expr->right, target_width);
    } else {
        // LCOV_EXCL_START
        if (var) {
            throw InternalException("Unable to fix width for " + var->handle_name());
        }
        // LCOV_EXCL_STOP
    }
}

std::shared_ptr<AssignStmt> EnumVar::assign_(const std::shared_ptr<Var> &var,
                                             kratos::AssignmentType type) {
    if (!var->is_enum())
        throw VarException("Cannot assign enum type to non enum type", {this, var.get()});
    if (var->type() == VarType::ConstValue) {
        auto p = var->as<EnumConst>();
        if (p->enum_def()->name != enum_type_->name)
            throw VarException("Cannot assign different enum type", {this, var.get()});
    } else {
        auto p = dynamic_cast<EnumType *>(var.get());
        if (!p) throw InternalException("Unable to obtain enum definition");
        if (!p->enum_type())
            throw VarException(::format("Cannot obtain enum information from var ({0}). "
                                        "Please use a cast if it's intended",
                                        var->handle_name()),
                               {var.get()});
        if (p->enum_type()->name != enum_type_->name) {
            throw VarException("Cannot assign different enum type", {this, var.get()});
        }
    }
    return Var::assign_(var, type);
}

FunctionCallVar::FunctionCallVar(Generator *m, const std::shared_ptr<FunctionStmtBlock> &func_def,
                                 const std::map<std::string, std::shared_ptr<Var>> &args,
                                 bool has_return)
    : Var(m, "", 1, 1, false), func_def_(func_def.get()), args_(args) {
    // check the function call types
    auto ports = func_def->ports();
    for (auto const &[port_name, func_port] : ports) {
        if (args.find(port_name) == args.end()) {
            throw VarException(::format("{0} is not connected", port_name), {func_port.get()});
        }
        // check the port types
        auto &arg_port = args.at(port_name);
        if (func_port->width() != arg_port->width())
            throw VarException(::format("{0}'s width doesn't match", port_name),
                               {func_port.get(), arg_port.get()});
        if (func_port->is_signed() != arg_port->is_signed())
            throw VarException(::format("{0}'s sign doesn't match", port_name),
                               {func_port.get(), arg_port.get()});
    }
    // compute the width and sign
    auto handle = func_def->function_handler();
    if (!handle && has_return && !func_def->is_dpi())
        throw StmtException(::format("{0} doesn't have return value", func_def->function_name()),
                            {func_def.get()});
    if (has_return && !func_def->is_dpi()) {
        var_width_ = handle->width();
        size_ = handle->size();
        is_signed_ = handle->is_signed();
    } else if (has_return && func_def->is_dpi()) {
        auto dpi = func_def->as<DPIFunctionStmtBlock>();
        if (dpi->return_width()) {
            var_width_ = dpi->return_width();
            // FIXME: always size 1?
            size_ = {1};
            is_signed_ = false;
        }
    }
}

void FunctionCallVar::add_sink(const std::shared_ptr<AssignStmt> &stmt) {
    for (auto const &iter : args_) {
        iter.second->add_sink(stmt);
    }
    // FIXME: this is a very hacky fix on constant generators
    if (generator() == Const::const_gen()) {
        // use left hand size of stmt
        generator_ = stmt->left()->generator();
        // change the function def to the new generator
        if (!generator()->has_function(func_def_->function_name())) {
            generator()->add_function(func_def_->as<FunctionStmtBlock>());
            generator()->add_call_var(as<FunctionCallVar>());
        }
    }
}

std::string FunctionCallVar::to_string() const {
    std::string result = func_def_->function_name() + " (";
    std::vector<std::string> names;
    names.reserve(args_.size());
    for (auto const &iter : args_) names.emplace_back(iter.second->to_string());
    // calling ordering
    if (!func_def_->port_ordering().empty()) {
        auto ordering = func_def_->port_ordering();
        std::unordered_map<std::string, uint32_t> indexing;
        indexing.reserve(ordering.size());
        for (auto const &[var_name, var] : args_) {
            indexing.emplace(var->to_string(), ordering.at(var_name));
        }
        std::sort(names.begin(), names.end(), [&](auto const &lhs, auto const &rhs) {
            return indexing.at(lhs) < indexing.at(rhs);
        });
    }
    result.append(string::join(names.begin(), names.end(), ", "));
    result.append(")");
    return result;
}

std::string InterfaceVar::to_string() const {
    std::string parent_name = interface_->name();
    return ::format("{0}.{1}", parent_name, Var::to_string());
}

std::string InterfaceVar::base_name() const { return interface_->base_name(); }

std::shared_ptr<Expr> util::mux(Var &cond, Var &left, Var &right) {
    auto expr = std::make_shared<ConditionalExpr>(cond.shared_from_this(), left.shared_from_this(),
                                                  right.shared_from_this());
    cond.generator()->add_expr(expr);
    return expr;
}

}  // namespace kratos
