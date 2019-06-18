#ifndef DUSK_EXPR_HH
#define DUSK_EXPR_HH

#include <set>
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
    Xor,

    // relational
    LessThan,
    GreaterThan,
    LessEqThan,
    GreaterEqThan,
    Eq
};

std::string ExprOpStr(ExprOp op);

enum VarType { Base, Expression, Slice };

enum AssignmentType { Blocking, NonBlocking, Undefined };

struct Var : public std::enable_shared_from_this<Var> {
public:
    Var(Generator *m, const std::string &name, uint32_t width, bool is_signed);
    Var(Generator *m, const std::string &name, uint32_t width, bool is_signed, VarType type);

    std::string name;
    uint32_t width;
    bool is_signed;

    // overload all the operators
    // unary
    Expr &operator~();
    Expr &operator-();
    Expr &operator+();
    // binary
    Expr &operator+(const Var &var);
    Expr &operator-(const Var &var);
    Expr &operator*(const Var &var);
    Expr &operator%(const Var &var);
    Expr &operator/(const Var &var);
    Expr &operator>>(const Var &var);
    Expr &operator<<(const Var &var);
    Expr &operator|(const Var &var);
    Expr &operator&(const Var &var);
    Expr &operator^(const Var &var);
    Expr &ashr(const Var &var);
    Expr &operator<(const Var &var);
    Expr &operator>(const Var &var);
    Expr &operator<=(const Var &var);
    Expr &operator>=(const Var &var);
    Expr &eq(const Var &var);
    // slice
    VarSlice &operator[](std::pair<uint32_t, uint32_t> slice);
    VarSlice &operator[](uint32_t bit);
    // assignment
    void assign(const std::shared_ptr<Var> &var) { assign(var, AssignmentType::Blocking); }
    void assign(Var &var) { assign(var, AssignmentType::Blocking); }
    void assign(const std::shared_ptr<Var> &var, AssignmentType type);
    void assign(Var &var, AssignmentType type);
    Var &operator=(const std::shared_ptr<Var> &var);

    Generator *generator;

    const std::shared_ptr<Var> src() const { return src_; }
    const std::set<std::shared_ptr<Var>> sinks() { return sinks_; }

    VarType type() const { return type_; }

    virtual std::string to_string();

protected:
    Var() : name(), width(), is_signed(false), generator(nullptr), type_(Base) {}

    std::shared_ptr<Var> src_ = nullptr;
    std::set<std::shared_ptr<Var>> sinks_;

    VarType type_ = VarType::Base;

private:
    std::pair<std::shared_ptr<Var>, std::shared_ptr<Var>> get_binary_var_ptr(const Var &var);
    std::map<std::pair<uint32_t, uint32_t>, VarSlice> slices_;

    AssignmentType assign_type_ = AssignmentType::Undefined;
};

struct VarSlice : public Var {
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
    std::string to_string() override;
};

#endif  // DUSK_EXPR_HH
