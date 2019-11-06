#ifndef KRATOS_EVAL_HH
#define KRATOS_EVAL_HH
#include "expr.hh"

namespace kratos {

uint64_t constexpr UINT64_MASK = 0xFFFFFFFFFFFFFFFF;

uint64_t invert(uint64_t value, uint32_t width);

uint64_t eval_bin_op(uint64_t left_value, uint64_t right_value, ExprOp op, uint32_t width,
                     bool signed_);
}  // namespace kratos

#endif  // KRATOS_EVAL_HH
