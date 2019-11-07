#include "eval.hh"

namespace kratos {

auto constexpr UINT64_WIDTH_ = 64;

uint64_t invert(uint64_t value, uint32_t width) {
    auto v = ~value;
    v ^= UINT64_MASK << width;
    return v;
}

uint64_t two_complement(uint64_t value, uint32_t width) {
    uint64_t inverted = invert(value, width) + 1;
    return inverted & (UINT64_MASK >> (UINT64_WIDTH_ - width));
}

uint64_t truncate(uint64_t value, uint32_t width) {
    return value & (UINT64_MASK >> (UINT64_WIDTH_ - width));
}

uint64_t eval_unary_op(uint64_t value, ExprOp op, uint32_t width) {
    switch(op) {
        case ExprOp::UMinus:
            return two_complement(value, width);
        case ExprOp::UAnd:
            return static_cast<uint32_t>(__builtin_popcount(value)) == width;
        case ExprOp::UInvert:
            return invert(value, width);
        case ExprOp::UNot:
             return !value;
        case ExprOp::UOr:
            return (bool)(value);
        case ExprOp::UPlus:
            return value;
        case ExprOp::UXor: {
            return __builtin_popcount(value) % 2;
        }
        default: throw std::runtime_error("Not implemented");
    }
}

uint64_t eval_bin_op(uint64_t left_value, uint64_t right_value, ExprOp op, uint32_t width,
                     bool signed_) {
    bool left_negative = signed_ && left_value >> (width - 1);
    bool right_negative = signed_ && right_value >> (width - 1);
    uint64_t left_abs_value = left_negative ? two_complement(left_value, width) : left_value;
    uint64_t right_abs_value = right_negative ? two_complement(right_value, width) : right_value;
    uint64_t signed_bit = static_cast<uint64_t>(left_negative ^ right_negative) << (width - 1);
    auto const mask = UINT64_MASK >> (64u - width);
    uint64_t result;
    switch (op) {
        case ExprOp::Add:
            result = left_value + right_value;
            break;
        case ExprOp::Minus:
            result = (left_value - right_value) & mask;
            break;
        case ExprOp::Multiply:
            result = left_abs_value * right_abs_value;
            if (signed_bit) result = two_complement(result, width);
            break;
        case ExprOp::Divide:
            result = left_abs_value / right_abs_value;
            if (signed_bit) result = two_complement(result, width);
            break;
        case ExprOp::And:
            result = left_value & right_value;
            break;
        case ExprOp::Or:
            result = left_value | right_value;
            break;
        case ExprOp::Xor:
            result = left_value ^ right_value;
            break;
        case ExprOp::Eq:
            result = left_value == right_value;
            break;
        case ExprOp::GreaterEqThan:
            result = left_abs_value >= right_abs_value;
            result = left_negative && !right_negative
                         ? false
                         : !left_negative && right_negative ? true : result ^ left_negative;
            break;
        case ExprOp::LessEqThan:
            result = left_abs_value <= right_abs_value;
            result = left_negative && !right_negative
                         ? true
                         : !left_negative && right_negative ? false : result ^ left_negative;
            break;
        case ExprOp::LessThan:
            result = left_abs_value < right_abs_value;
            result = left_negative && !right_negative
                         ? true
                         : !left_negative && right_negative ? false : result ^ left_negative;
            break;
        case ExprOp ::GreaterThan:
            result = left_abs_value > right_abs_value;
            result = left_negative && !right_negative
                         ? false
                         : !left_negative && right_negative ? true : result ^ left_negative;
            break;
        case ExprOp::SignedShiftRight:
            result = left_abs_value >> right_value;
            if (left_negative) result |= UINT64_MASK << (width - 1 - right_value);
            break;
        case ExprOp::LogicalShiftRight:
            result = left_value >> right_value;
            break;
        default: {
            throw std::runtime_error("Not implemented");
        }
    }
    result = result & (UINT64_MASK >> (64 - width));
    return result;
}
}