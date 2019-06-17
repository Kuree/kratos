#include "expr.hh"
#include <stdexcept>
#include "fmt/format.h"
#include "generator.hh"
#include "io.hh"

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

Expr& Var::operator-(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::Minus, left, right);
}

Expr& Var::operator-() {
    auto var = generator->get_var(name);
    return generator->expr(ExprOp::Minus, var, nullptr);
}

Expr& Var::operator~() {
    auto var = generator->get_var(name);
    return generator->expr(ExprOp::UInvert, var, nullptr);
}

Expr& Var::operator+() {
    auto var = generator->get_var(name);
    return generator->expr(ExprOp::UPlus, var, nullptr);
}

Expr& Var::operator+(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::Add, left, right);
}

Expr& Var::operator*(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::Multiply, left, right);
}

Expr& Var::operator%(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::Mod, left, right);
}

Expr& Var::operator/(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::Divide, left, right);
}

Expr& Var::operator>>(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::LogicalShiftRight, left, right);
}

Expr& Var::operator<<(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::ShiftLeft, left, right);
}

Expr& Var::operator|(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::Or, left, right);
}

Expr& Var::operator&(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::And, left, right);
}

Expr& Var::operator^(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::Xor, left, right);
}

Expr& Var::ashr(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return generator->expr(ExprOp::SignedShiftRight, left, right);
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
    if (slices_.find(slice) != slices_.end()) return slices_.at(slice);
    // create a new one
    slices_.emplace(slice, VarSlice(this, high, low));
    return slices_.at(slice);
}

VarSlice &Var::operator[](uint32_t bit) { return (*this)[{bit, bit}]; }

VarSlice::VarSlice(Var *parent, uint32_t high, uint32_t low)
    : Var(parent->generator, ::format("{0}[{1}:{2}]", parent->name, high, low), high - low + 1,
          parent->is_signed) {}


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
}

Var::Var(Generator *module, std::string name, uint32_t width, bool is_signed)
    : name(std::move(name)), width(width), is_signed(is_signed), generator(module) {}
