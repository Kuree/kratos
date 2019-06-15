#include "expr.hh"
#include <stdexcept>
#include "absl/strings/str_format.h"
#include "absl/strings/str_split.h"
#include "io.hh"
#include "module.hh"

using absl::StrFormat;
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

Var::Var(const Var &var) {
    name = var.name;
    width = var.width;
    is_signed = var.is_signed;
    context = var.context;
}

std::pair<Var *, Var *> Var::get_binary_var_ptr(const Var &var) {
    auto left = context->get_var(name);
    if (left == nullptr)
        throw std::runtime_error(::StrFormat("unable to find port %s from context", var.name));
    auto right = context->get_var(var.name);
    if (right == nullptr)
        throw std::runtime_error(::StrFormat("unable to find port %s from context", var.name));
    return {left, right};
}

Expr Var::operator-(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return Expr(ExprOp::Minus, left, right);
}

Expr Var::operator-() {
    auto var = context->get_var(name);
    return Expr(ExprOp::Minus, var, nullptr);
}

Expr Var::operator~() {
    auto var = context->get_var(name);
    return Expr(ExprOp::UInvert, var, nullptr);
}

Expr Var::operator+() {
    auto var = context->get_var(name);
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

Expr::Expr(ExprOp op, Var *left, Var *right) : op(op), left(left), right(right) {
    if (left == nullptr) throw std::runtime_error("left operand is null");
    if (right != nullptr && left->context != right->context)
        throw std::runtime_error(
            ::StrFormat("%s context is different from that of %s's", left->name, right->name));
    context = left->context;
    if (right != nullptr && left->width != right->width)
        throw std::runtime_error(
            ::StrFormat("left (%s) width (%d) doesn't match with right (%s) width (%d", left->name,
                        left->width, right->name, right->width));
    width = left->width;
    if (right != nullptr)
        name = ::StrFormat("(%s %s %s)", left->name, ExprOpStr(op), right->name);
    else
        name = ::StrFormat("(%s %s)", ExprOpStr(op), left->name);
    if (right != nullptr)
        is_signed = left->is_signed | right->is_signed;
    else
        is_signed = left->is_signed;

    // add it to context's vars
    context->add_var(*this);
}

Var::Var(Context *c, std::string name, uint32_t width, bool is_signed)
    : name(std::move(name)), width(width), is_signed(is_signed), context(c) {}
