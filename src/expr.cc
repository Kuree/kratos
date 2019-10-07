#include "expr.hh"
#include <algorithm>
#include <iostream>
#include <stdexcept>
#include "except.hh"
#include "fmt/format.h"
#include "generator.hh"
#include "stmt.hh"
#include "syntax.hh"
#include "util.hh"

using fmt::format;
using std::make_shared;
using std::runtime_error;
using std::shared_ptr;
using std::string;
using std::vector;

namespace kratos {

bool is_relational_op(ExprOp op) {
    static std::unordered_set<ExprOp> ops = {ExprOp::LessThan, ExprOp::GreaterThan,
                                             ExprOp::LessEqThan, ExprOp::GreaterEqThan, ExprOp::Eq};
    return ops.find(op) != ops.end();
}

std::pair<std::shared_ptr<Var>, std::shared_ptr<Var>> Var::get_binary_var_ptr(
    const Var &var) const {
    auto left = const_cast<Var *>(this)->shared_from_this();
    auto right = const_cast<Var *>(&var)->shared_from_this();
    return {left, right};
}

Expr &Var::operator-(const Var &var) const {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::Minus, left, right);
}

Expr &Var::operator-() const {
    auto var = generator->get_var(name);
    return generator->expr(ExprOp::Minus, var, nullptr);
}

Expr &Var::operator~() const {
    auto var = generator->get_var(name);
    return generator->expr(ExprOp::UInvert, var, nullptr);
}

Expr &Var::operator+() const {
    auto var = generator->get_var(name);
    return generator->expr(ExprOp::UPlus, var, nullptr);
}

Expr &Var::r_or() const {
    auto var = generator->get_var(name);
    return generator->expr(ExprOp::UOr, var, nullptr);
}
Expr &Var::r_and() const {
    auto var = generator->get_var(name);
    return generator->expr(ExprOp::UAnd, var, nullptr);
}
Expr &Var::r_xor() const {
    auto var = generator->get_var(name);
    return generator->expr(ExprOp::UXor, var, nullptr);
}
Expr &Var::r_not() const {
    auto var = generator->get_var(name);
    return generator->expr(ExprOp::UNot, var, nullptr);
}

Expr &Var::operator+(const Var &var) const {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::Add, left, right);
}

Expr &Var::operator*(const Var &var) const {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::Multiply, left, right);
}

Expr &Var::operator%(const Var &var) const {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::Mod, left, right);
}

Expr &Var::operator/(const Var &var) const {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::Divide, left, right);
}

Expr &Var::operator>>(const Var &var) const {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::LogicalShiftRight, left, right);
}

Expr &Var::operator<<(const Var &var) const {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::ShiftLeft, left, right);
}

Expr &Var::operator|(const Var &var) const {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::Or, left, right);
}

Expr &Var::operator&(const Var &var) const {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::And, left, right);
}

Expr &Var::operator^(const Var &var) const {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::Xor, left, right);
}

Expr &Var::ashr(const Var &var) const {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::SignedShiftRight, left, right);
}

Expr &Var::operator<(const Var &var) const {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::LessThan, left, right);
}

Expr &Var::operator>(const Var &var) const {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::GreaterThan, left, right);
}

Expr &Var::operator<=(const Var &var) const {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::LessEqThan, left, right);
}

Expr &Var::operator>=(const Var &var) const {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::GreaterEqThan, left, right);
}

Expr &Var::eq(const Var &var) const {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::Eq, left, right);
}

Expr &Var::operator!=(const Var &var) const {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::Neq, left, right);
}

VarSlice &Var::operator[](std::pair<uint32_t, uint32_t> slice) {
    auto const [high, low] = slice;
    if (low > high) {
        throw VarException(::format("low ({0}) cannot be larger than ({1})", low, high), {this});
    }
    // if the size is not 1, we are slicing off size, not width
    if (size_ == 1) {
        if (high >= width()) {
            throw VarException(
                ::format("high ({0}) has to be smaller than width ({1})", high, width()), {this});
        }
    } else {
        if (high > size_) {
            throw VarException(
                ::format("high ({0}) has to be smaller than size ({1})", high, size_), {this});
        }
    }
    // create a new one
    // notice that slice is not part of generator's variables. It's handled by the parent (var)
    // itself
    auto var_slice = ::make_shared<VarSlice>(this, high, low);
    slices_.emplace(var_slice);
    return *var_slice;
}

VarSlice &Var::operator[](const std::shared_ptr<Var> &var) {
    auto var_slice = ::make_shared<VarVarSlice>(this, var.get());
    slices_.emplace(var_slice);
    return *var_slice;
}

VarConcat &Var::concat(Var &var) {
    auto ptr = var.shared_from_this();
    // notice that we effectively created an implicit sink->sink by creating a concat
    // however, it's not an assignment, that's why we need to use concat_vars to hold the
    // vars
    for (auto const &exist_var : concat_vars_) {
        // reuse the existing variables
        if (exist_var->vars().size() == 2 && exist_var->vars().back() == ptr) {
            return *exist_var;
        }
    }
    auto concat_ptr = std::make_shared<VarConcat>(shared_from_this(), ptr);
    concat_vars_.emplace(concat_ptr);
    return *concat_ptr;
}

std::string Var::to_string() const { return name; }

std::string Var::handle_name() const { return handle_name(false); }

std::string Var::handle_name(bool ignore_top) const {
    auto gen_name = generator->handle_name(ignore_top);
    if (!gen_name.empty())
        return ::format("{0}.{1}", generator->handle_name(ignore_top), to_string());
    else
        return to_string();
}

void Var::set_width_param(const std::shared_ptr<Param> &param) { set_width_param(param.get()); }

void Var::set_width_param(kratos::Param *param) {
    // set width to the current param value
    if (param->value() <= 0) {
        throw VarException(::format("{0} is non-positive ({1}), "
                                    "thus cannot be used for parametrization width",
                                    param->to_string()),
                           {param});
    }
    var_width_ = param->value();
    param_ = param;
    param->add_param_var(this);
}

VarSlice &Var::operator[](uint32_t bit) { return this->operator[]({bit, bit}); }

VarSlice::VarSlice(Var *parent, uint32_t high, uint32_t low)
    : Var(parent->generator, "", parent->var_width(), 1, parent->is_signed(), VarType::Slice),
      parent_var(parent),
      low(low),
      high(high),
      op_({high, low}) {
    // compute the width
    if (parent->size() == 1) {
        // this is the actual slice
        var_width_ = high - low + 1;
    } else {
        size_ = high - low + 1;
        var_width_ = parent->var_width();
    }
    // compute the var high and var_low
    if (parent->type() != VarType::Slice) {
        // use width to compute
        if (parent->size() == 1) {
            var_low_ = low;
            var_high_ = high;
        } else {
            var_low_ = low * parent->var_width();
            var_high_ = (high + 1) * parent->var_width() - 1;
        }
    } else {
        // it's a slice
        if (parent->size() == 1) {
            auto slice = dynamic_cast<VarSlice *>(parent);
            var_low_ = low + slice->var_low();
            var_high_ = (high + 1) + slice->var_low();
        } else {
            auto slice = dynamic_cast<VarSlice *>(parent);
            var_low_ = slice->var_low() + low * parent->var_width();
            var_high_ = slice->var_low() + (high + 1) * parent->var_width() - 1;
        }
    }
}

std::string VarSlice::get_slice_name(const std::string &parent_name, uint32_t high, uint32_t low) {
    if (high == low)
        return ::format("{0}[{1}]", parent_name, high);
    else
        return ::format("{0}[{1}:{2}]", parent_name, high, low);
}

std::string VarSlice::to_string() const {
    return get_slice_name(parent_var->to_string(), high, low);
}

const Var *VarSlice::get_var_root_parent() const {
    Var *parent = parent_var;
    while (parent->type() == VarType::Slice) {
        parent = parent->as<VarSlice>()->parent_var;
    }
    return parent;
}

VarVarSlice::VarVarSlice(kratos::Var *parent, kratos::Var *slice)
    : VarSlice(parent, 0, 0), sliced_var_(slice) {
    // check the size or width
    // we need to re-compute var_high, var_low, width, and other stuff by ourselves here
    // there is an issue about the var_high and var_low; the problem will only show up during
    // the connectivity check
    // TODO: fix this
    if (parent->size() == 1) {
        // slice through the 1D array
        // so the width will be 1
        var_width_ = 1;
        size_ = 1;
        var_high_ = 0;
        var_low_ = 0;
    } else {
        var_width_ = parent->var_width();
        size_ = 1;
        var_high_ = var_width_ - 1;
        var_low_ = 0;
        // we need to compute the clog2 here
        uint32_t required_width = std::ceil(std::log2(parent->size()));
        if (required_width != sliced_var_->width()) {
            // error message copied from verilator
            throw VarException(
                ::format("Bit extraction of array[{0}:0] requires {1} bit index, not {2} bits.",
                         parent->size() - 1, required_width, sliced_var_->width()),
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
    sliced_var_->add_source(stmt);
}

std::string VarVarSlice::to_string() const {
    return ::format("{0}[{1}]", parent_var->to_string(), sliced_var_->to_string());
}

Expr::Expr(ExprOp op, const ::shared_ptr<Var> &left, const ::shared_ptr<Var> &right)
    : Var(left->generator, "", left->var_width(), left->size(), left->is_signed()),
      op(op),
      left(left),
      right(right) {
    if (left == nullptr) throw UserException("left operand is null");

    if (right != nullptr && left->width() != right->width())
        throw VarException(
            ::format("left ({0}) width ({1}) doesn't match with right ({2}) width ({3})",
                     left->to_string(), left->width(), right->to_string(), right->width()),
            {left.get(), right.get()});
    // if it's a predicate/relational op, the width is one
    if (is_relational_op(op))
        var_width_ = 1;
    else
        var_width_ = left->width();

    if (right != nullptr)
        is_signed_ = left->is_signed() & right->is_signed();
    else
        is_signed_ = left->is_signed();
    type_ = VarType::Expression;
    set_parent();
}

Expr::Expr(const std::shared_ptr<Var> &left, std::shared_ptr<Var> right)
    : Var(left->generator, "", left->width() / left->size(), left->size(), left->is_signed()),
      op(ExprOp::Add),
      left(left),
      right(std::move(right)) {
    type_ = VarType::Expression;
    set_parent();
}

void Expr::set_parent() {
    // compute the right parent for the expr
    // it can only go up
    if (!right) {
        generator = left->generator;
    } else {
        auto left_gen = left->generator;
        auto right_gen = right->generator;
        if (left_gen == Const::const_gen()) {
            generator = right_gen;
        } else if (right_gen == Const::const_gen()) {
            generator = left_gen;
        } else if (left_gen == right_gen) {
            generator = left->generator;
        } else {
            // choose the higher/lower one based on the var type
            if (left_gen == right_gen->parent() && right->type() == PortIO) {
                generator = left_gen;
            } else if (left_gen->parent() == right_gen->parent() && left->type() == PortIO &&
                       right->type() == PortIO) {
                generator = dynamic_cast<Generator *>(left_gen->parent());
            } else {
                generator = right_gen;
            }
        }
    }
}

Var::Var(Generator *module, const std::string &name, uint32_t var_width, uint32_t size,
         bool is_signed)
    : Var(module, name, var_width, size, is_signed, VarType::Base) {}

Var::Var(Generator *module, const std::string &name, uint32_t var_width, uint32_t size,
         bool is_signed, VarType type)
    : IRNode(IRNodeKind::VarKind),
      name(name),
      generator(module),
      var_width_(var_width),
      size_(size),
      is_signed_(is_signed),
      type_(type) {
    // only constant allows to be null generator
    if (module == nullptr && type != VarType::ConstValue)
        throw UserException(::format("module is null for {0}", name));
    if (!is_valid_variable_name(name))
        throw UserException(::format("{0} is a SystemVerilog keyward", name));
}

IRNode *Var::parent() { return generator; }
IRNode *VarSlice::parent() { return parent_var; }

std::shared_ptr<AssignStmt> Var::assign(const std::shared_ptr<Var> &var) {
    return assign(var, AssignmentType::Undefined);
}

std::shared_ptr<AssignStmt> Var::assign(Var &var) {
    return assign(var.shared_from_this(), AssignmentType::Undefined);
}

std::shared_ptr<AssignStmt> Var::assign(const std::shared_ptr<Var> &var, AssignmentType type) {
    // if it's a constant or expression, it can't be assigned to
    if (type_ == VarType::ConstValue)
        throw VarException(::format("Cannot assign {0} to a const {1}", var->to_string(), name),
                           {this, var.get()});
    else if (type_ == VarType::Expression)
        throw VarException(::format("Cannot assign {0} to an expression", var->to_string(), name),
                           {this, var.get()});
    auto const &stmt = ::make_shared<AssignStmt>(shared_from_this(), var, type);

    return stmt;
}

void Var::unassign(const std::shared_ptr<AssignStmt> &stmt) {
    // we need to take care of the slices
    stmt->right()->sinks_.erase(stmt);
    sources_.erase(stmt);
    // erase from parent if any
    // TODO: fix this will proper parent
    generator->remove_stmt(stmt);
}

Const::Const(Generator *generator, int64_t value, uint32_t width, bool is_signed)
    : Var(generator, std::to_string(value), width, 1, is_signed, VarType::ConstValue), value_() {
    // need to deal with the signed value
    if (is_signed) {
        // compute the -max value
        uint64_t temp = (~0ull) << (width - 1);
        int64_t min = 0;
        std::memcpy(&min, &temp, sizeof(min));
        if (value < min)
            throw UserException(::format(
                "{0} is smaller than the minimum value ({1}) given width {2}", value, min, width));
        temp = (1ull << (width - 1)) - 1;
        int64_t max;
        std::memcpy(&max, &temp, sizeof(max));
        if (value > max)
            throw UserException(::format(
                "{0} is larger than the maximum value ({1}) given width {2}", value, max, width));
    } else {
        uint64_t max = (1ull << width) - 1;
        uint64_t unsigned_value;
        std::memcpy(&unsigned_value, &value, sizeof(unsigned_value));
        if (unsigned_value > max)
            throw UserException(::format(
                "{0} is larger than the maximum value ({1}) given width {2}", value, max, width));
    }
    value_ = value;
}

Const::Const(int64_t value, uint32_t width, bool is_signed)
    : Const(nullptr, value, width, is_signed) {
    if (!const_generator_) const_generator_ = std::make_shared<Generator>(nullptr, "");
    generator = const_generator_.get();
}

Const &Const::constant(int64_t value, uint32_t width, bool is_signed) {
    auto p = std::make_shared<Const>(value, width, is_signed);
    consts_.emplace(p);
    return *p;
}

std::unordered_set<std::shared_ptr<Const>> Const::consts_ = {};
std::shared_ptr<Generator> Const::const_generator_ = nullptr;

VarCasted::VarCasted(Var *parent, VarCastType cast_type)
    : Var(parent->generator, "", parent->width(), true, parent->type()),
      parent_var_(parent),
      cast_type_(cast_type) {
    type_ = VarType::BaseCasted;
    if (cast_type_ == Signed) {
        is_signed_ = true;
    } else if (cast_type_ == Unsigned) {
        is_signed_ = false;
    } else if (cast_type_ == VarCastType::AsyncReset || cast_type_ == VarCastType::Clock) {
        if (parent->size() != 1) {
            throw VarException(::format("Can only cast bit width 1 to "
                                        "Clock or AsyncReset. {0} is {1}",
                                        parent->to_string(), parent->size()),
                               {parent});
        }
    }
}

std::shared_ptr<AssignStmt> VarCasted::assign(const std::shared_ptr<Var> &, AssignmentType) {
    throw VarException(::format("{0} is not allowed to be a sink", to_string()), {this});
}

std::string VarCasted::to_string() const {
    if (cast_type_ == VarCastType::Signed)
        return ::format("signed'({0})", parent_var_->to_string());
    else if (cast_type_ == VarCastType::Unsigned)
        return ::format("unsigned'({0})", parent_var_->to_string());
    else
        return parent_var_->to_string();
}

void VarCasted::add_sink(const std::shared_ptr<AssignStmt> &stmt) { parent_var_->add_sink(stmt); }

std::shared_ptr<Var> Var::cast(VarCastType cast_type) {
    if (cast_type == VarCastType::Signed && is_signed_) {
        return shared_from_this();
    } else if (casted_.find(cast_type) != casted_.end()) {
        return casted_.at(cast_type);
    } else {
        casted_.emplace(cast_type, std::make_shared<VarCasted>(this, cast_type));
        return casted_.at(cast_type);
    }
}

void Const::set_value(int64_t new_value) {
    try {
        Const c(generator, new_value, width(), is_signed_);
        value_ = new_value;
    } catch (::runtime_error &) {
        std::cerr << ::format("Unable to set value from {0} to {1}", value_, new_value)
                  << std::endl;
    }
}

void Const::add_source(const std::shared_ptr<AssignStmt> &) {
    throw VarException(::format("const {0} is not allowed to be driven by a net", to_string()),
                       {this});
}

void Const::add_sink(const std::shared_ptr<AssignStmt> &stmt) {
    auto left = stmt->left();
    // if it's a port, we change the constant's generator to that of port
    auto generator = left->generator;
    if (!generator)
        throw StmtException(::format("Unable to find left hand side generator"), {stmt.get()});
    auto parent = generator->parent();
    if (parent && parent->ir_node_kind() == GeneratorKind) {
        auto gen = dynamic_cast<Generator *>(parent);
        this->generator = gen;
    }
}

Param::Param(Generator *m, std::string name, uint32_t width, bool is_signed)
    : Const(m, 0, width, is_signed), parameter_name_(std::move(name)) {
    // override the type value
    type_ = VarType::Parameter;
}

void Param::set_value(int64_t new_value) {
    if (new_value <= 0 && !param_vars_.empty()) {
        throw VarException(
            ::format(
                "{0} is used for parametrizing variable width, thus cannot be non-positive ({1})",
                to_string(), new_value),
            {this});
    }
    Const::set_value(new_value);

    // change the width of parametrized variables
    for (auto &var : param_vars_) {
        var->var_width() = new_value;
    }
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
    auto content = join(var_names.begin(), var_names.end(), ", ");
    return ::format("{{{0}}}", content);
}

VarConcat::VarConcat(const std::shared_ptr<VarConcat> &first, const std::shared_ptr<Var> &second)
    : Expr(first, second) {
    if (first->is_signed_ != second->is_signed())
        throw VarException(
            ::format("{0} is signed but {1} is not", first->to_string(), second->to_string()),
            {first.get(), second.get()});
    vars_ = std::vector<std::shared_ptr<Var>>(first->vars_.begin(), first->vars_.end());
    vars_.emplace_back(second);
    var_width_ = first->width() + second->width();
    op = ExprOp::Concat;
}

VarConcat::VarConcat(const std::shared_ptr<Var> &first, const std::shared_ptr<Var> &second)
    : Expr(first, second) {
    if (first->is_signed() != second->is_signed())
        throw VarException(
            ::format("{0} is signed but {1} is not", first->to_string(), second->to_string()),
            {first.get(), second.get()});
    vars_ = {first, second};
    var_width_ = first->width() + second->width();
    op = ExprOp::Concat;
}

VarConcat &VarConcat::concat(kratos::Var &var) {
    auto result = std::make_shared<VarConcat>(as<VarConcat>(), var.shared_from_this());
    // add it to the first one
    vars_[0]->add_concat_var(result);
    return *result;
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
                                  bool ignore_top = false) {
    auto left = expr->left;
    auto right = expr->right;

    auto left_str = left->type() == VarType::Expression
                        ? expr_to_string(left->as<Expr>().get(), expr->op == left->as<Expr>()->op,
                                         use_handle, ignore_top)
                        : (use_handle ? left->handle_name(ignore_top) : left->to_string());

    if (right != nullptr) {
        auto right_str =
            right->type() == VarType::Expression
                ? expr_to_string(right->as<Expr>().get(), expr->op == right->as<Expr>()->op,
                                 use_handle, ignore_top)
                : (use_handle ? right->handle_name(ignore_top) : right->to_string());
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

IRNode *Expr::get_child(uint64_t index) {
    if (index == 0)
        return left.get();
    else if (index == 1)
        return right ? right.get() : nullptr;
    else
        return nullptr;
}

void set_var_parent(std::shared_ptr<Var> &var, Var *target, Var *new_var, bool check_target) {
    std::shared_ptr<VarSlice> slice;
    std::shared_ptr<Var> parent_var = var;
    std::vector<std::shared_ptr<VarSlice>> slices;
    while (parent_var->type() == VarType::Slice) {
        // this is for nested slicing
        slice = parent_var->as<VarSlice>();
        slices.emplace_back(slice);
        parent_var = slice->parent_var->shared_from_this();
    }
    if (parent_var.get() != target) {
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
    var = new_var_ptr;
}

void change_var_expr(const std::shared_ptr<Expr> &expr, Var *target, Var *new_var) {
    if (expr->left->type() == VarType::Expression) {
        change_var_expr(expr->left->as<Expr>(), target, new_var);
    }
    if (expr->right && expr->right->type() == VarType::Expression) {
        change_var_expr(expr->right->as<Expr>(), target, new_var);
    }

    if (expr->left.get() == target) expr->left = new_var->shared_from_this();
    if (expr->right && expr->right.get() == target) expr->right = new_var->shared_from_this();

    // need to change the parent as well
    if (expr->left->type() == VarType::Slice) {
        set_var_parent(expr->left, target, new_var, false);
    }
    if (expr->right && expr->right->type() == VarType::Slice) {
        set_var_parent(expr->right, target, new_var, false);
    }
}

void stmt_set_right(AssignStmt *stmt, Var *target, Var *new_var) {
    auto &right = stmt->right();
    if (right->type() == VarType::Base || right->type() == VarType::PortIO ||
        right->type() == VarType::ConstValue) {
        if (right.get() == target)
            stmt->set_right(new_var->shared_from_this());
        else
            throw InternalException("Target not found");
    } else if (right->type() == VarType::Slice) {
        set_var_parent(right, target, new_var, true);
    } else if (right->type() == VarType::Expression) {
        change_var_expr(stmt->right()->as<Expr>(), target, new_var);
    }
}

void stmt_set_left(AssignStmt *stmt, Var *target, Var *new_var) {
    auto &left = stmt->left();
    if (left->type() == VarType::Base || left->type() == VarType::PortIO ||
        left->type() == VarType::ConstValue) {
        if (left.get() == target)
            stmt->set_left(new_var->shared_from_this());
        else
            throw InternalException("Target not found");
    } else if (left->type() == VarType::Slice) {
        set_var_parent(left, target, new_var, true);
    } else if (left->type() == VarType::Expression) {
        change_var_expr(stmt->left()->as<Expr>(), target, new_var);
    }
}

void Var::move_src_to(Var *var, Var *new_var, Generator *parent, bool keep_connection) {
    // only base and port vars are allowed
    if (var->type_ == VarType::Expression || var->type_ == VarType::ConstValue)
        throw VarException("Only base or port variables are allowed.", {var, new_var});

    for (auto &stmt : var->sources_) {
        if (stmt->generator_parent() != parent) continue;
        stmt_set_left(stmt.get(), var, new_var);
        if (parent->debug) {
            stmt->fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
        }
        new_var->add_source(stmt);
    }
    // now clear the sources
    var->sources_.clear();

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

    for (auto &stmt : var->sinks_) {
        if (stmt->generator_parent() != parent) {
            continue;
        }
        stmt_set_right(stmt.get(), var, new_var);
        if (parent->debug) {
            stmt->fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
        }
        new_var->add_sink(stmt);
    }
    // now clear the sinks
    var->sinks_.clear();

    if (keep_connection) {
        // create an assignment and add it to the parent
        auto stmt = new_var->assign(var->shared_from_this());
        if (parent->debug) {
            stmt->fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
        }
        parent->add_stmt(stmt);
    }
}

void Expr::add_sink(const std::shared_ptr<AssignStmt> &stmt) {
    left->add_sink(stmt);
    if (right) right->add_sink(stmt);
}

void VarSlice::add_sink(const std::shared_ptr<AssignStmt> &stmt) {
    Var *parent = parent_var;
    while (parent->type() == VarType::Slice) {
        auto ptr = reinterpret_cast<VarSlice *>(parent);
        parent = ptr->parent_var;
    }
    parent->add_sink(stmt);
}

void VarSlice::add_source(const std::shared_ptr<AssignStmt> &stmt) {
    Var *parent = parent_var;
    while (parent->type() == VarType::Slice) {
        auto ptr = reinterpret_cast<VarSlice *>(parent);
        parent = ptr->parent_var;
    }
    parent->add_source(stmt);
}

ConditionalExpr::ConditionalExpr(const std::shared_ptr<Var> &condition,
                                 const std::shared_ptr<Var> &left,
                                 const std::shared_ptr<Var> &right)
    : Expr(ExprOp::Conditional, left, right), condition(condition) {
    if (condition->width() != 1)
        throw VarException("Ternary operator's condition has to be a binary value",
                           {condition.get()});
}

IRNode *ConditionalExpr::get_child(uint64_t index) {
    if (index == 0)
        return condition.get();
    else if (index == 1)
        return left.get();
    else if (index == 2)
        return right.get();
    else
        return nullptr;
}

void ConditionalExpr::add_sink(const std::shared_ptr<AssignStmt> &stmt) {
    condition->add_sink(stmt);
    left->add_sink(stmt);
    right->add_sink(stmt);
}

std::string ConditionalExpr::to_string() const {
    return ::format("{0} ? {1}: {2}", condition->to_string(), left->to_string(),
                    right->to_string());
}

std::string ConditionalExpr::handle_name(bool ignore_top) const {
    return ::format("{0} ? {1}: {2}", condition->handle_name(ignore_top),
                    left->handle_name(ignore_top), right->handle_name(ignore_top));
}

PackedStruct::PackedStruct(std::string struct_name,
                           std::vector<std::tuple<std::string, uint32_t, bool>> attributes)
    : struct_name(std::move(struct_name)), attributes(std::move(attributes)) {}

PackedSlice::PackedSlice(PortPacked *parent, const std::string &member_name)
    : VarSlice(parent, 0, 0), member_name_(member_name) {
    auto const &struct_ = parent->packed_struct();
    set_up(struct_, member_name);
}

PackedSlice::PackedSlice(kratos::VarPacked *parent, const std::string &member_name)
    : VarSlice(parent, 0, 0), member_name_(member_name) {
    auto const &struct_ = parent->packed_struct();
    set_up(struct_, member_name);
}

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
    if (var->type() == PortIO) {
        auto v = var->as<PortPacked>();
        return v->operator[](member_name_).shared_from_this();
    } else {
        auto v = var->as<VarPacked>();
        return v->operator[](member_name_).shared_from_this();
    }
}

std::string PackedSlice::to_string() const {
    return ::format("{0}.{1}", parent_var->to_string(), member_name_);
}

PackedSlice &VarPacked::operator[](const std::string &member_name) {
    auto ptr = std::make_shared<PackedSlice>(this, member_name);
    slices_.emplace(ptr);
    return *ptr;
}

VarPacked::VarPacked(Generator *m, const std::string &name, PackedStruct packed_struct_)
    : Var(m, name, 0, 1, false), struct_(std::move(packed_struct_)) {
    // compute the width
    uint32_t width = 0;
    for (auto const &def : struct_.attributes) {
        width += std::get<1>(def);
    }
    var_width_ = width;
}

std::set<std::string> VarPacked::member_names() const {
    std::set<std::string> result;
    for (auto const &def : struct_.attributes) {
        result.emplace(std::get<0>(def));
    }
    return result;
}

Enum::Enum(kratos::Generator *generator, std::string name,
           const std::map<std::string, uint64_t> &values, uint32_t width)
    : name(std::move(name)), width_(width) {
    for (auto const &[n, value] : values) {
        auto c = std::make_shared<EnumConst>(generator, value, width, this, n);
        this->values.emplace(n, c);
    }
}

std::shared_ptr<EnumConst> Enum::get_enum(const std::string &enum_name) {
    if (values.find(enum_name) == values.end())
        throw UserException(::format("Cannot find {0} in {1}", enum_name, name));
    return values.at(enum_name);
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

std::shared_ptr<AssignStmt> EnumVar::assign(const std::shared_ptr<Var> &var,
                                            kratos::AssignmentType type) {
    if (!var->is_enum())
        throw VarException("Cannot assign enum type to non enum type", {this, var.get()});
    if (var->type() == VarType::ConstValue) {
        auto p = var->as<EnumConst>();
        if (p->enum_def()->name != enum_type_->name)
            throw VarException("Cannot assign different enum type", {this, var.get()});
    } else {
        auto p = var->as<EnumVar>();
        if (p->enum_type_->name != enum_type_->name) {
            throw VarException("Cannot assign different enum type", {this, var.get()});
        }
    }
    return Var::assign(var, type);
}

FunctionCallVar::FunctionCallVar(Generator *m, const std::shared_ptr<FunctionStmtBlock> &func_def,
                                 const std::map<std::string, std::shared_ptr<Var>> &args,
                                 bool has_return)
    : Var(m, "", 0, 0, false), func_def_(func_def.get()), args_(args) {
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
            size_ = 1;
            is_signed_ = false;
        }
    }
}

void FunctionCallVar::add_sink(const std::shared_ptr<AssignStmt> &stmt) {
    for (auto const &iter : args_) {
        iter.second->add_sink(stmt);
    }
    // FIXME: this is a very hacky fix on constant generators
    if (generator == Const::const_gen()) {
        // use left hand size of stmt
        generator = stmt->left()->generator;
        // change the function def to the new generator
        if (!generator->has_function(func_def_->function_name())) {
            generator->add_function(func_def_->as<FunctionStmtBlock>());
            generator->add_call_var(as<FunctionCallVar>());
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
    result.append(join(names.begin(), names.end(), ", "));
    result.append(")");
    return result;
}

}  // namespace kratos
