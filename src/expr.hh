#ifndef DUSK_EXPR_HH
#define DUSK_EXPR_HH

#include <string>
#include "context.hh"

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


std::string ExprOpStr(ExprOp op);

struct Var {
public:
    Var(Context *c, std::string name, uint32_t width, bool is_signed);
    Var(const Var &var);

    std::string name;
    uint32_t width;
    bool is_signed;

    // overload all the operators
    // unary
    Expr operator~();
    Expr operator-();
    Expr operator+();
    // binary
    Expr operator+(const Var &var);
    Expr operator-(const Var &var);
    Expr operator*(const Var &var);
    Expr operator%(const Var &var);
    Expr operator/(const Var &var);
    Expr operator>>(const Var &var);
    Expr operator<<(const Var &var);
    Expr operator|(const Var &var);
    Expr operator&(const Var &var);
    Expr operator^(const Var &var);
    Expr ashr(const Var &var);

    Context *context;

protected:
    Var(): name(), width(), is_signed(false), context(nullptr) {}

private:
    std::pair<Var*, Var*> get_binary_var_ptr(const Var &var);
};


struct Expr : public Var {
    ExprOp op;
    Var *left;
    Var *right;
    Expr(ExprOp op, Var *left, Var *right);

};

#endif  // DUSK_EXPR_HH
