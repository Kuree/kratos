#include "eval.hh"

namespace kratos {

uint64_t invert(uint64_t value, uint32_t width) {
    auto v = ~value;
    v ^= UINT64_MASK << width;
    return v;
}

uint64_t eval_bin_op(uint64_t left_value, uint64_t right_value, ExprOp op, uint32_t width,
                     bool signed_) {
    bool left_negative = signed_ && left_value >> (width - 1);
    bool right_negative = signed_ && right_value >> (width - 1);
    uint64_t left_abs_value =
        left_negative ? (left_negative ^ (UINT64_MASK << (width - 1))) : left_value;
    uint64_t right_abs_value =
        right_negative ? (right_negative ^ (UINT64_MASK << (width - 1))) : width;
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
        case ExprOp::And:
            result = left_value & right_value;
            break;
        case ExprOp::Divide:
            result = left_abs_value / right_abs_value;
            result |= signed_bit;
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
        case ExprOp::LogicalShiftRight:
            result = left_abs_value >> right_value;
            if (left_negative) result |= UINT64_MASK << (width - 1 - right_value);
            break;
        default: {
            throw std::runtime_error("Not implemented");
        }
    }
    result = result & (UINT64_MASK >> (64 - width));
    return result;
}
}