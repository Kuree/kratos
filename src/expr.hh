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

struct Var: public std::enable_shared_from_this<Var> {
public:
    Var(Generator *m, std::string name, uint32_t width, bool is_signed);

    std::string name;
    uint32_t width;
    bool is_signed;

    // overload all the operators
    // unary
    Expr& operator~();
    Expr& operator-();
    Expr& operator+();
    // binary
    Expr& operator+(const Var &var);
    Expr& operator-(const Var &var);
    Expr& operator*(const Var &var);
    Expr& operator%(const Var &var);
    Expr& operator/(const Var &var);
    Expr& operator>>(const Var &var);
    Expr& operator<<(const Var &var);
    Expr& operator|(const Var &var);
    Expr& operator&(const Var &var);
    Expr& operator^(const Var &var);
    Expr& ashr(const Var &var);


    VarSlice &operator[](std::pair<uint32_t, uint32_t> slice);
    VarSlice &operator[](uint32_t bit);

    Generator *generator;

protected:
    Var() : name(), width(), is_signed(false), generator(nullptr) {}


private:
    std::pair<std::shared_ptr<Var>, std::shared_ptr<Var>> get_binary_var_ptr(const Var &var);
    std::map<std::pair<uint32_t, uint32_t>, VarSlice> slices_;
};


struct VarSlice: public Var {
public:
    Var *parent = nullptr;
    uint32_t low = 0;
    uint32_t high = 0;

    VarSlice(Var *parent, uint32_t high, uint32_t low);
};

struct Expr : public Var {
    ExprOp op;
    std::shared_ptr<Var> left;
    std::shared_ptr<Var> right;

    Expr(ExprOp op, const std::shared_ptr<Var> &left, const std::shared_ptr<Var> &right);
};

#endif  // DUSK_EXPR_HH
