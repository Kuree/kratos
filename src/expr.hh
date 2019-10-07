#ifndef KRATOS_EXPR_HH
#define KRATOS_EXPR_HH

#include <set>
#include <string>
#include <unordered_set>
#include <vector>
#include "context.hh"
#include "ir.hh"

namespace kratos {

enum ExprOp : uint64_t {
    // unary
    UInvert,
    UMinus,
    UPlus,
    UOr,
    UNot,
    UAnd,
    UXor,

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
    Eq,
    Neq,

    // ternary
    Conditional,

    // special
    Concat
};

bool is_relational_op(ExprOp op);

enum VarType { Base, Expression, Slice, ConstValue, PortIO, Parameter, BaseCasted };

enum VarCastType { Signed, Unsigned, Clock, AsyncReset };

struct Var : public std::enable_shared_from_this<Var>, public IRNode {
public:
    Var(Generator *m, const std::string &name, uint32_t var_width, uint32_t size, bool is_signed);
    Var(Generator *m, const std::string &name, uint32_t var_width, uint32_t size, bool is_signed,
        VarType type);

    std::string name;
    uint32_t &var_width() { return var_width_; }
    uint32_t &size() { return size_; }
    bool &is_signed() { return is_signed_; };
    uint32_t width() const { return var_width_ * size_; };
    uint32_t var_width() const { return var_width_; }
    uint32_t size() const { return size_; }
    bool is_signed() const { return is_signed_; };

    // overload all the operators
    // unary
    Expr &operator~() const;
    Expr &operator-() const;
    Expr &operator+() const;
    Expr &r_or() const;
    Expr &r_and() const;
    Expr &r_xor() const;
    Expr &r_not() const;
    // binary
    Expr &operator+(const Var &var) const;
    Expr &operator-(const Var &var) const;
    Expr &operator*(const Var &var) const;
    Expr &operator%(const Var &var) const;
    Expr &operator/(const Var &var) const;
    Expr &operator>>(const Var &var) const;
    Expr &operator<<(const Var &var) const;
    Expr &operator|(const Var &var) const;
    Expr &operator&(const Var &var) const;
    Expr &operator^(const Var &var) const;
    Expr &ashr(const Var &var) const;
    Expr &operator<(const Var &var) const;
    Expr &operator>(const Var &var) const;
    Expr &operator<=(const Var &var) const;
    Expr &operator>=(const Var &var) const;
    Expr &operator!=(const Var &var) const;
    Expr &eq(const Var &var) const;
    // slice
    virtual VarSlice &operator[](std::pair<uint32_t, uint32_t> slice);
    virtual VarSlice &operator[](uint32_t bit);
    virtual VarSlice &operator[](const std::shared_ptr<Var> &var);
    // concat
    virtual VarConcat &concat(Var &var);

    std::shared_ptr<Var> cast(VarCastType cast_type);

    // assignment
    std::shared_ptr<AssignStmt> assign(const std::shared_ptr<Var> &var);
    std::shared_ptr<AssignStmt> assign(Var &var);
    virtual std::shared_ptr<AssignStmt> assign(const std::shared_ptr<Var> &var,
                                               AssignmentType type);
    std::shared_ptr<AssignStmt> assign(Var &var, AssignmentType type);
    void unassign(const std::shared_ptr<AssignStmt> &stmt);

    Generator *generator;
    IRNode *parent() override;

    VarType type() const { return type_; }
    const std::unordered_set<std::shared_ptr<AssignStmt>> &sinks() const { return sinks_; };
    void remove_sink(const std::shared_ptr<AssignStmt> &stmt) { sinks_.erase(stmt); }
    const std::unordered_set<std::shared_ptr<AssignStmt>> &sources() const { return sources_; };
    void remove_source(const std::shared_ptr<AssignStmt> &stmt) { sources_.erase(stmt); }
    std::set<std::shared_ptr<VarSlice>> &get_slices() { return slices_; }

    static void move_src_to(Var *var, Var *new_var, Generator *parent, bool keep_connection);
    static void move_sink_to(Var *var, Var *new_var, Generator *parent, bool keep_connection);
    virtual void add_sink(const std::shared_ptr<AssignStmt> &stmt) { sinks_.emplace(stmt); }
    virtual void add_source(const std::shared_ptr<AssignStmt> &stmt) { sources_.emplace(stmt); }
    void add_concat_var(const std::shared_ptr<VarConcat> &var) { concat_vars_.emplace(var); }

    template <typename T>
    std::shared_ptr<T> as() {
        return std::static_pointer_cast<T>(shared_from_this());
    }

    virtual bool inline is_packed() const { return false; }
    virtual bool inline is_enum() const { return false; }
    virtual bool inline is_function() const { return false; }
    virtual std::shared_ptr<Var> slice_var(std::shared_ptr<Var> var) { return var; }

    virtual std::string to_string() const;

    // AST stuff
    void accept(IRVisitor *visitor) override { visitor->visit(this); }
    uint64_t child_count() override { return 0; }
    IRNode *get_child(uint64_t) override { return nullptr; }

    // meta info
    // packed is only relevant when the size is larger than 1, by default it's false
    bool packed_array = false;
    std::string handle_name() const;
    virtual std::string handle_name(bool ignore_top) const;
    // is parametrized
    bool parametrized() const { return param_ != nullptr; }
    void set_width_param(const std::shared_ptr<Param> &param);
    void set_width_param(Param *param);
    Param *param() const { return param_; }

    // for slice
    virtual const Var *get_var_root_parent() const { return this; }

    // before and after strings. they're used for downstream tools. kratos doesn't care about the
    // value. it's user's responsibility to make it legal syntax
    inline void set_before_var_str_(const std::string &value) { before_var_str_ = value; }
    inline const std::string &before_var_str() const { return before_var_str_; }
    inline void set_after_var_str_(const std::string &value) { after_var_str_ = value; }
    inline const std::string &after_var_str() const { return after_var_str_; }

    Var(const Var &var) = delete;
    Var() = delete;

    ~Var() override = default;

protected:
    uint32_t var_width_;
    uint32_t size_;
    bool is_signed_;

    std::unordered_set<std::shared_ptr<AssignStmt>> sinks_;
    std::unordered_set<std::shared_ptr<AssignStmt>> sources_;

    VarType type_ = VarType::Base;

    std::unordered_set<std::shared_ptr<VarConcat>> concat_vars_;

    std::set<std::shared_ptr<VarSlice>> slices_;

    // comment values
    std::string before_var_str_;
    std::string after_var_str_;

    // parametrization
    Param *param_ = nullptr;

private:
    std::pair<std::shared_ptr<Var>, std::shared_ptr<Var>> get_binary_var_ptr(const Var &var) const;

    std::unordered_map<VarCastType, std::shared_ptr<VarCasted>> casted_;
};

struct VarCasted : public Var {
public:
    VarCasted(Var *parent, VarCastType cast_type);
    std::shared_ptr<AssignStmt> assign(const std::shared_ptr<Var> &var,
                                       AssignmentType type) override;

    void add_sink(const std::shared_ptr<AssignStmt> &stmt) override;

    std::string to_string() const override;

    VarCastType cast_type() const { return cast_type_; }

private:
    Var *parent_var_ = nullptr;

    VarCastType cast_type_;
};

struct VarSlice : public Var {
public:
    Var *parent_var = nullptr;
    uint32_t low = 0;
    uint32_t high = 0;

    VarSlice(Var *parent, uint32_t high, uint32_t low);
    IRNode *parent() override;

    // we tie it to the parent
    void add_sink(const std::shared_ptr<AssignStmt> &stmt) override;
    void add_source(const std::shared_ptr<AssignStmt> &stmt) override;

    void set_parent(Var *parent) { parent_var = parent; }

    void accept(IRVisitor *visitor) override { visitor->visit(this); }

    static std::string get_slice_name(const std::string &parent_name, uint32_t high, uint32_t low);

    std::string to_string() const override;

    uint32_t var_high() { return var_high_; }
    uint32_t var_low() { return var_low_; }

    std::shared_ptr<Var> slice_var(std::shared_ptr<Var> var) override {
        return var->operator[](op_).shared_from_this();
    }

    const Var *get_var_root_parent() const override;
    virtual bool sliced_by_var() const { return false; }

protected:
    uint32_t var_high_ = 0;
    uint32_t var_low_ = 0;

    std::pair<uint32_t, uint32_t> op_;
};

struct VarVarSlice : public VarSlice {
    // the name is a little bit funny
public:
    VarVarSlice(Var *parent, Var *slice);

    std::string to_string() const override;

    void add_sink(const std::shared_ptr<AssignStmt> &stmt) override;
    void add_source(const std::shared_ptr<AssignStmt> &stmt) override;

    std::shared_ptr<Var> slice_var(std::shared_ptr<Var> var) override {
        return var->operator[](sliced_var_->shared_from_this()).shared_from_this();
    }

    bool sliced_by_var() const override { return true; }

private:
    Var *sliced_var_;
};

struct Const : public Var {
    // need to rewrite the const backend since the biggest number is uint64_t, which may not
public:
    Const(Generator *m, int64_t value, uint32_t width, bool is_signed);

    int64_t value() const { return value_; }
    virtual void set_value(int64_t new_value);
    void add_source(const std::shared_ptr<AssignStmt> &stmt) override;
    void add_sink(const std::shared_ptr<AssignStmt> &stmt) override;

    std::string to_string() const override;

    void accept(IRVisitor *visitor) override { visitor->visit(this); }

    static Const &constant(int64_t value, uint32_t width, bool is_signed);
    Const(int64_t value, uint32_t width, bool is_signed);

    static const Generator *const_gen() { return const_generator_.get(); }

private:
    int64_t value_;
    // created without a generator holder
    static std::unordered_set<std::shared_ptr<Const>> consts_;
    static std::shared_ptr<Generator> const_generator_;
};

// helper function
inline Const &constant(int64_t value, uint32_t width, bool is_signed = false) {
    return Const::constant(value, width, is_signed);
}

struct Param : public Const {
public:
    Param(Generator *m, std::string name, uint32_t width, bool is_signed);

    void accept(IRVisitor *visitor) override { visitor->visit(this); }

    std::string inline to_string() const override { return parameter_name_; }

    std::string inline value_str() const { return Const::to_string(); }

    const std::unordered_set<Var*> &param_vars() const { return param_vars_; }
    void add_param_var(Var *var) { param_vars_.emplace(var); }
    void set_value(int64_t new_value) override;

private:
    std::string parameter_name_;

    std::unordered_set<Var*> param_vars_;
};

struct PackedStruct {
public:
    std::string struct_name;
    std::vector<std::tuple<std::string, uint32_t, bool>> attributes;

    PackedStruct(std::string struct_name,
                 std::vector<std::tuple<std::string, uint32_t, bool>> attributes);
};

struct PackedSlice : public VarSlice {
public:
    PackedSlice(PortPacked *parent, const std::string &member_name);
    PackedSlice(VarPacked *parent, const std::string &member_name);

    std::string to_string() const override;

    std::shared_ptr<Var> slice_var(std::shared_ptr<Var> var) override;

private:
    void set_up(const PackedStruct &struct_, const std::string &member_name);
    std::string member_name_;
};

struct PackedInterface {
    [[nodiscard]] virtual std::set<std::string> member_names() const = 0;
    virtual ~PackedInterface() = default;
};

struct VarPacked : public Var, public PackedInterface {
public:
    VarPacked(Generator *m, const std::string &name, PackedStruct packed_struct_);

    bool is_packed() const override { return true; }

    const PackedStruct &packed_struct() const { return struct_; }

    PackedSlice &operator[](const std::string &member_name);

    // necessary to make pybind happy due to complex inheritance
    VarSlice inline &operator[](std::pair<uint32_t, uint32_t> slice) override {
        return Var::operator[](slice);
    }
    VarSlice inline &operator[](uint32_t idx) override { return Var::operator[](idx); }

    std::set<std::string> member_names() const override;

private:
    PackedStruct struct_;
};

struct Expr : public Var {
public:
    ExprOp op;
    std::shared_ptr<Var> left;
    std::shared_ptr<Var> right;

    Expr(ExprOp op, const std::shared_ptr<Var> &left, const std::shared_ptr<Var> &right);
    std::string to_string() const override;
    void add_sink(const std::shared_ptr<AssignStmt> &stmt) override;

    // AST
    void accept(IRVisitor *visitor) override { visitor->visit(this); }
    uint64_t child_count() override { return right ? 2 : 1; }
    IRNode *get_child(uint64_t index) override;

    std::string handle_name(bool ignore_top) const override;

protected:
    // caller is responsible for the op
    Expr(const std::shared_ptr<Var> &left, std::shared_ptr<Var> right);

private:
    void set_parent();
};

struct VarConcat : public Expr {
public:
    VarConcat(const std::shared_ptr<Var> &first, const std::shared_ptr<Var> &second);
    VarConcat(const std::shared_ptr<VarConcat> &first, const std::shared_ptr<Var> &second);

    // we tie it to the parent
    void add_sink(const std::shared_ptr<AssignStmt> &stmt) override;
    void add_source(const std::shared_ptr<AssignStmt> &stmt) override;

    std::vector<std::shared_ptr<Var>> &vars() { return vars_; }

    VarConcat &concat(Var &var) override;

    void accept(IRVisitor *visitor) override { visitor->visit(this); }

    std::string to_string() const override;

private:
    std::vector<std::shared_ptr<Var>> vars_;
};

struct ConditionalExpr : public Expr {
    ConditionalExpr(const std::shared_ptr<Var> &condition, const std::shared_ptr<Var> &left,
                    const std::shared_ptr<Var> &right);
    uint64_t child_count() override { return 3; }
    IRNode *get_child(uint64_t index) override;
    void add_sink(const std::shared_ptr<AssignStmt> &stmt) override;
    std::string to_string() const override;
    std::string handle_name(bool ignore_top) const override;

    std::shared_ptr<Var> condition;
};

struct EnumConst : public Const {
public:
    EnumConst(Generator *m, int64_t value, uint32_t width, Enum *parent, std::string name);
    std::string to_string() const override;
    std::string value_string() { return Const::to_string(); }

    bool inline is_enum() const override { return true; }
    const inline Enum *enum_def() const { return parent_; }

    void accept(IRVisitor *visitor) override { visitor->visit(this); }

private:
    Enum *parent_;
    std::string name_;
};

struct Enum : std::enable_shared_from_this<Enum> {
public:
    Enum(Generator *generator, std::string name, const std::map<std::string, uint64_t> &values,
         uint32_t width);
    std::map<std::string, std::shared_ptr<EnumConst>> values;
    std::string name;

    uint32_t inline width() { return width_; }

    std::shared_ptr<EnumConst> get_enum(const std::string &name);
    void add_debug_info(const std::string &enum_name,
                        const std::pair<std::string, uint32_t> &debug);

private:
    uint32_t width_;
};

struct EnumVar : public Var {
public:
    bool inline is_enum() const override { return true; }

    EnumVar(Generator *m, const std::string &name, const std::shared_ptr<Enum> &enum_type)
        : Var(m, name, enum_type->width(), 1, false), enum_type_(enum_type.get()) {}

    std::shared_ptr<AssignStmt> assign(const std::shared_ptr<Var> &var,
                                       AssignmentType type) override;

    const inline Enum *enum_type() const { return enum_type_; }
    void accept(IRVisitor *visitor) override { visitor->visit(this); }

private:
    Enum *enum_type_;
};

struct FunctionCallVar : public Var {
public:
    FunctionCallVar(Generator *m, const std::shared_ptr<FunctionStmtBlock> &func_def,
                    const std::map<std::string, std::shared_ptr<Var>> &args,
                    bool has_return = true);
    bool is_function() const override { return true; }
    FunctionStmtBlock *func() { return func_def_; }

    VarSlice &operator[](std::pair<uint32_t, uint32_t>) override {
        throw std::runtime_error("Slice a function call is not allowed");
    };
    VarSlice &operator[](uint32_t) override {
        throw std::runtime_error("Slice a function call is not allowed");
    };

    std::string to_string() const override;

    void add_sink(const std::shared_ptr<AssignStmt> &stmt) override;
    void add_source(const std::shared_ptr<AssignStmt> &) override {
        throw std::runtime_error("Slice a function call is not allowed");
    }

    void accept(IRVisitor *visitor) override { visitor->visit(this); }

    const std::map<std::string, std::shared_ptr<Var>> &args() const { return args_; }

private:
    FunctionStmtBlock *func_def_;
    std::map<std::string, std::shared_ptr<Var>> args_;
};

}  // namespace kratos
#endif  // KRATOS_EXPR_HH
