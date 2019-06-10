#ifndef DUSK_EXPR_HH
#define DUSK_EXPR_HH

enum ExprOp {
    // unary
    UInvert,
    UMinus,
    UPlus,

    // binary
    Add,
    Minus,
    Divide,
    Multiply,
    Mod,
    LogicalShiftRight,
    SignedShiftRight,
    ShiftLeft,
    Or,
    And,
    Xor
};


inline std::string ExprOpStr(ExprOp op) {
    switch(op) {
        case UInvert: return "uinvert";
        case UMinus: return "usub";
        case UPlus: return "uplus";
        case Add: return "add";
        case Minus: return "sub";
        case Divide: return "div";
        case Multiply: return "mul";
        case Mod: return "mod";
        case LogicalShiftRight: return "lshr";
        case SignedShiftRight: return "ashr";
        case ShiftLeft: return "shl";
        case Or: return "or";
        case And: return "and";
        case Xor: return "xor";
        default:
            throw std::runtime_error("unable to find op");
    }
}

#endif  // DUSK_EXPR_HH
