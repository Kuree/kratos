#ifndef KRATOS_EXPR_HH
#define KRATOS_EXPR_HH

#include <set>
#include <string>
#include <unordered_set>
#include <vector>
#include "ast.hh"
#include "context.hh"

enum ExprOp : uint64_t {
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

bool is_relational_op(ExprOp op);

std::string ExprOpStr(ExprOp op);

enum VarType { Base, Expression, Slice, ConstValue, PortIO };

struct Var : public std::enable_shared_from_this<Var>, public ASTNode {
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
    // concat
    virtual VarConcat &concat(Var &var);
    std::unordered_set<std::shared_ptr<VarConcat>> concat_vars;

    // assignment
    AssignStmt &assign(const std::shared_ptr<Var> &var);
    AssignStmt &assign(Var &var);
    AssignStmt &assign(const std::shared_ptr<Var> &var, AssignmentType type);
    AssignStmt &assign(Var &var, AssignmentType type);
    void unassign(const std::shared_ptr<Var> &var);

    Generator *generator;
    ASTNode *parent() override;

    VarType type() const { return type_; }
    std::unordered_set<std::shared_ptr<AssignStmt>> sinks() const { return sinks_; };
    std::unordered_set<std::shared_ptr<AssignStmt>> sources() const { return sources_; };
    std::map<std::pair<uint32_t, uint32_t>, std::shared_ptr<VarSlice>> &get_slices() {
        return slices_;
    }

    static void move_src_to(Var *var, Var *new_var, Generator *parent);
    static void move_sink_to(Var *var, Var *new_var, Generator *parent);

    template <typename T>
    std::shared_ptr<T> as() {
        return std::static_pointer_cast<T>(shared_from_this());
    }

    virtual std::string to_string() const;

    // AST stuff
    void accept(ASTVisitor *visitor) override { visitor->visit(this); }
    uint64_t child_count() override { return 0; }
    ASTNode *get_child(uint64_t) override { return nullptr; }

protected:
    Var()
        : ASTNode(ASTNodeKind::VarKind),
          name(),
          width(),
          is_signed(false),
          generator(nullptr),
          type_(Base) {}

    std::unordered_set<std::shared_ptr<AssignStmt>> sinks_;
    std::unordered_set<std::shared_ptr<AssignStmt>> sources_;

    VarType type_ = VarType::Base;

private:
    std::pair<std::shared_ptr<Var>, std::shared_ptr<Var>> get_binary_var_ptr(const Var &var);
    std::map<std::pair<uint32_t, uint32_t>, std::shared_ptr<VarSlice>> slices_;
};

struct VarSlice : public Var {
public:
    Var *parent_var = nullptr;
    uint32_t low = 0;
    uint32_t high = 0;

    VarSlice(Var *parent, uint32_t high, uint32_t low);
    ASTNode *parent() override;

    void accept(ASTVisitor *visitor) override { visitor->visit(this); }

    static std::string get_slice_name(const std::string &parent_name, uint32_t high, uint32_t low);

    std::string to_string() const override;
};

struct VarConcat : public Var {
public:
    std::vector<std::shared_ptr<Var>> vars;
    VarConcat(Generator *m, const std::shared_ptr<Var> &first, const std::shared_ptr<Var> &second);
    VarConcat(const VarConcat &var);

    VarConcat &concat(Var &var) override;
    void accept(ASTVisitor *visitor) override { visitor->visit(this); }

    std::string to_string() const override;
};

struct Const : public Var {
    // need to rewrite the const backend since the biggest number is uint64_t, which may not
public:
    Const(Generator *m, int64_t value, uint32_t width, bool is_signed);

    int64_t value() { return value_; }

    std::string to_string() const override;

    void accept(ASTVisitor *visitor) override { visitor->visit(this); }

private:
    int64_t value_;
};

struct Expr : public Var {
    ExprOp op;
    std::shared_ptr<Var> left;
    std::shared_ptr<Var> right;

    Expr(ExprOp op, const std::shared_ptr<Var> &left, const std::shared_ptr<Var> &right);
    std::string to_string() const override;

    // AST
    void accept(ASTVisitor *visitor) override { visitor->visit(this); }
    uint64_t child_count() override { return right ? 2 : 1; }
    ASTNode *get_child(uint64_t index) override;
};

#endif  // KRATOS_EXPR_HH
