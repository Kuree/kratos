#include "expr.hh"
#include <stdexcept>
#include "fmt/format.h"
#include "io.hh"
#include "module.hh"

using fmt::format;
using std::runtime_error;
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
        default:
            throw std::runtime_error("unable to find op");
    }
}

std::pair<Var *, Var *> Var::get_binary_var_ptr(const Var &var) {
    auto left = module->get_var(name);
    if (left == nullptr)
        throw std::runtime_error(::format("unable to find port %s from context", var.name));
    auto right = module->get_var(var.name);
    if (right == nullptr)
        throw std::runtime_error(::format("unable to find port %s from context", var.name));
    return {left, right};
}

Expr Var::operator-(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return Expr(ExprOp::Minus, left, right);
}

Expr Var::operator-() {
    auto var = module->get_var(name);
    return Expr(ExprOp::Minus, var, nullptr);
}

Expr Var::operator~() {
    auto var = module->get_var(name);
    return Expr(ExprOp::UInvert, var, nullptr);
}

Expr Var::operator+() {
    auto var = module->get_var(name);
    return Expr(ExprOp::UPlus, var, nullptr);
}

Expr Var::operator+(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return Expr(ExprOp::Add, left, right);
}

Expr Var::operator*(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return Expr(ExprOp::Multiply, left, right);
}

Expr Var::operator%(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return Expr(ExprOp::Mod, left, right);
}

Expr Var::operator/(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return Expr(ExprOp::Divide, left, right);
}

Expr Var::operator>>(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return Expr(ExprOp::LogicalShiftRight, left, right);
}

Expr Var::operator<<(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return Expr(ExprOp::ShiftLeft, left, right);
}

Expr Var::operator|(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return Expr(ExprOp::Or, left, right);
}

Expr Var::operator&(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return Expr(ExprOp::And, left, right);
}

Expr Var::operator^(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return Expr(ExprOp::Xor, left, right);
}

Expr Var::ashr(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return Expr(ExprOp::SignedShiftRight, left, right);
}

VarSlice &Var::operator[](std::pair<uint32_t, uint32_t> slice) {
    auto const [high, low] = slice;
    if (low > high) {
        throw ::runtime_error(::format("low (%d) cannot be larger than (%d)", low, high));
    }
    if (high >= width) {
        throw ::runtime_error(::format("high (%d) has to be smaller than width (%d)", high, width));
    }
    // if we already has the slice
    if (slices_.find(slice) != slices_.end())
        return slices_.at(slice);
    // create a new one
    slices_.emplace(slice, VarSlice(this, high, low));
    return slices_.at(slice);
}

VarSlice &Var::operator[](uint32_t bit) { return (*this)[{bit, bit}]; }

VarSlice::VarSlice(Var *parent, uint32_t high, uint32_t low)
    : Var(parent->module, ::format("%s[%d:%d]", parent->name, high, low), high - low + 1,
          parent->is_signed) {}

Expr::Expr(ExprOp op, Var *left, Var *right) : op(op), left(left), right(right) {
    if (left == nullptr) throw std::runtime_error("left operand is null");
    if (right != nullptr && left->module != right->module)
        throw std::runtime_error(
            ::format("%s context is different from that of %s's", left->name, right->name));
    module = left->module;
    if (right != nullptr && left->width != right->width)
        throw std::runtime_error(
            ::format("left (%s) width (%d) doesn't match with right (%s) width (%d", left->name,
                     left->width, right->name, right->width));
    width = left->width;
    if (right != nullptr)
        name = ::format("(%s %s %s)", left->name, ExprOpStr(op), right->name);
    else
        name = ::format("(%s %s)", ExprOpStr(op), left->name);
    if (right != nullptr)
        is_signed = left->is_signed | right->is_signed;
    else
        is_signed = left->is_signed;


    // add it to context's vars
    module->add_expr(*this);
}

Var::Var(Module *module, std::string name, uint32_t width, bool is_signed)
    : name(std::move(name)), width(width), is_signed(is_signed), module(module) {}
