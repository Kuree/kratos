#include "expr.hh"
#include <stdexcept>
#include "fmt/format.h"
#include "generator.hh"
#include "stmt.hh"

using fmt::format;
using std::make_shared;
using std::runtime_error;
using std::shared_ptr;
using std::string;
using std::vector;

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
        default:
            throw std::runtime_error("unable to find op");
    }
}

std::pair<std::shared_ptr<Var>, std::shared_ptr<Var>> Var::get_binary_var_ptr(const Var &var) {
    auto left = generator->get_var(name);
    if (left == nullptr)
        throw std::runtime_error(
            ::format("unable to find port {0} from {1}", var.name, var.generator->name));
    auto right = generator->get_var(var.name);
    if (right == nullptr)
        throw std::runtime_error(
            ::format("unable to find port {0} from {1}", var.name, var.generator->name));
    return {left, right};
}

Expr &Var::operator-(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::Minus, left, right);
}

Expr &Var::operator-() {
    auto var = generator->get_var(name);
    return generator->expr(ExprOp::Minus, var, nullptr);
}

Expr &Var::operator~() {
    auto var = generator->get_var(name);
    return generator->expr(ExprOp::UInvert, var, nullptr);
}

Expr &Var::operator+() {
    auto var = generator->get_var(name);
    return generator->expr(ExprOp::UPlus, var, nullptr);
}

Expr &Var::operator+(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::Add, left, right);
}

Expr &Var::operator*(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::Multiply, left, right);
}

Expr &Var::operator%(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::Mod, left, right);
}

Expr &Var::operator/(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::Divide, left, right);
}

Expr &Var::operator>>(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::LogicalShiftRight, left, right);
}

Expr &Var::operator<<(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::ShiftLeft, left, right);
}

Expr &Var::operator|(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::Or, left, right);
}

Expr &Var::operator&(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::And, left, right);
}

Expr &Var::operator^(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::Xor, left, right);
}

Expr &Var::ashr(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::SignedShiftRight, left, right);
}

Expr &Var::operator<(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::LessThan, left, right);
}

Expr &Var::operator>(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::GreaterThan, left, right);
}

Expr &Var::operator<=(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::LessEqThan, left, right);
}

Expr &Var::operator>=(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::GreaterEqThan, left, right);
}

Expr &Var::eq(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::Eq, left, right);
}

VarSlice &Var::operator[](std::pair<uint32_t, uint32_t> slice) {
    auto const [high, low] = slice;
    if (low > high) {
        throw ::runtime_error(::format("low ({0}) cannot be larger than ({1})", low, high));
    }
    if (high >= width) {
        throw ::runtime_error(
            ::format("high ({0}) has to be smaller than width ({1})", high, width));
    }
    // if we already has the slice
    if (slices_.find(slice) != slices_.end()) return *slices_.at(slice);
    // create a new one
    // notice that slice is not part of generator's variables. It's handled by the parent (var)
    // itself
    auto var_slice = ::make_shared<VarSlice>(this, high, low);
    slices_.emplace(slice, var_slice);
    return *slices_.at(slice);
}

std::string Var::to_string() { return name; }

VarSlice &Var::operator[](uint32_t bit) { return (*this)[{bit, bit}]; }

VarSlice::VarSlice(Var *parent, uint32_t high, uint32_t low)
    : Var(parent->generator, ::format("{0}[{1}:{2}]", parent->name, high, low), high - low + 1,
          parent->is_signed, VarType::Slice),
      parent(parent),
      low(low),
      high(high) {}

Expr::Expr(ExprOp op, const ::shared_ptr<Var> &left, const ::shared_ptr<Var> &right)
    : op(op), left(left), right(right) {
    if (left == nullptr) throw std::runtime_error("left operand is null");
    if (right != nullptr && left->generator != right->generator)
        throw std::runtime_error(
            ::format("{0} context is different from that of {1}'s", left->name, right->name));
    generator = left->generator;
    if (right != nullptr && left->width != right->width)
        throw std::runtime_error(
            ::format("left ({0}) width ({1}) doesn't match with right ({2}) width ({3})",
                     left->name, left->width, right->name, right->width));
    width = left->width;
    if (right != nullptr)
        name = ::format("({0} {1} {2})", left->name, ExprOpStr(op), right->name);
    else
        name = ::format("({0} {1})", ExprOpStr(op), left->name);
    if (right != nullptr)
        is_signed = left->is_signed & right->is_signed;
    else
        is_signed = left->is_signed;
    type_ = VarType::Expression;
}

Var::Var(Generator *module, const std::string &name, uint32_t width, bool is_signed)
    : Var(module, name, width, is_signed, VarType::Base) {}

Var::Var(Generator *module, const std::string &name, uint32_t width, bool is_signed, VarType type)
    : name(name), width(width), is_signed(is_signed), generator(module), type_(type) {
    if (module == nullptr) throw ::runtime_error(::format("module is null for {0}", name));
}

std::string assign_type_name(AssignmentType type) {
    switch (type) {
        case AssignmentType::Blocking:
            return "blocking";
        case AssignmentType ::NonBlocking:
            return "non-blocking";
        default:
            return "unknown";
    }
}

AssignStmt &Var::assign(const std::shared_ptr<Var> &var) {
    return assign(var, AssignmentType::Undefined);
}

AssignStmt &Var::assign(Var &var) { return assign(var, AssignmentType::Undefined); }

AssignStmt &Var::assign(const std::shared_ptr<Var> &var, AssignmentType type) {
    auto const &stmt = ::make_shared<AssignStmt>(shared_from_this(), var, type);
    // determine the type
    AssignmentType self_type = AssignmentType::Undefined;
    for (auto const &sink : sinks_) {
        if (sink->assign_type() != AssignmentType::Undefined) {
            self_type = sink->assign_type();
            break;
        }
    }
    // push the stmt into its sinks
    sinks_.emplace(stmt);
    if (self_type == AssignmentType::Undefined) self_type = type;
    // check if the assignment match existing ones
    for (auto const &sink : sinks_) {
        if (sink->assign_type() != self_type)
            throw ::runtime_error(
                ::format("{0}'s assignment type ({1}) does not match with {2}'s {3}", var->name,
                         assign_type_name(type), name, assign_type_name(self_type)));
    }
    return *stmt;
}

Const::Const(Generator *generator, int64_t value, uint32_t width, bool is_signed)
    : Var(generator, ::format("{0}", value), width, is_signed, VarType::ConstValue), value_() {
    // need to deal with the signed value
    if (is_signed) {
        // compute the -max value
        uint64_t temp = (~0ull) << (width - 1);
        int64_t min = 0;
        std::memcpy(&min, &temp, sizeof(min));
        if (value < min)
            throw ::runtime_error(::format(
                "{0} is smaller than the minimum value ({1}) given width {2}", value, min, width));
        temp = (1ull << (width - 1) )- 1;
        int64_t max;
        std::memcpy(&max, &temp, sizeof(max));
        if (value > max)
            throw ::runtime_error(::format(
                "{0} is larger than the maximum value ({1}) given width {2}", value, max, width));
    } else {
        uint64_t max = (1ull << width) - 1;
        uint64_t unsigned_value;
        std::memcpy(&unsigned_value, &value, sizeof(unsigned_value));
        if (unsigned_value > max)
            throw ::runtime_error(::format(
                "{0} is larger than the maximum value ({1}) given width {2}", value, max, width));
    }
    value_ = value;
}

std::string Const::to_string() {
    if (is_signed && value_ < 0) {
        return ::format("-{0}'h{1:X}", width, -value_);
    } else {
        return ::format("{0}'h{1:X}", width, value_);
    }
}

AssignStmt &Var::assign(Var &var, AssignmentType type) {
    // need to find the pointer
    auto var_ptr = var.shared_from_this();
    return assign(var_ptr, type);
}

std::string Expr::to_string() {
    if (right != nullptr) {
        return ::format("{0} {1} {2}", left->name, ExprOpStr(op), right->name);
    } else {
        return ::format("{0} {1}", ExprOpStr(op), left->name);
    }
}