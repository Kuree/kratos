#ifndef KRATOS_EXPR_HH
#define KRATOS_EXPR_HH

#include <set>
#include <stdexcept>
#include <string>
#include <unordered_set>
#include <vector>

#include "context.hh"
#include "ir.hh"

namespace kratos {

enum class ExprOp : uint64_t {
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
    // logical
    LAnd,
    LOr,

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
    Concat,
    Extend
};

bool is_relational_op(ExprOp op);
bool is_reduction_op(ExprOp op);
bool is_expand_op(ExprOp op);
bool is_unary_op(ExprOp op);

enum class VarType { Base, Expression, Slice, ConstValue, PortIO, Parameter, BaseCasted };

enum class VarCastType { Signed, Unsigned, Clock, AsyncReset, Enum };

struct Var : public std::enable_shared_from_this<Var>, public IRNode {
public:
    Var(Generator *m, const std::string &name, uint32_t var_width, uint32_t size, bool is_signed);
    Var(Generator *m, const std::string &name, uint32_t var_width,
        const std::vector<uint32_t> &size, bool is_signed);
    Var(Generator *m, const std::string &name, uint32_t var_width, uint32_t size, bool is_signed,
        VarType type);
    Var(Generator *m, const std::string &name, uint32_t var_width, std::vector<uint32_t> size,
        bool is_signed, VarType type);

    std::string name;
    uint32_t &var_width() { return var_width_; }
    std::vector<uint32_t> &size() { return size_; }
    const std::vector<uint32_t> &size() const { return size_; }
    bool &is_signed() { return is_signed_; };
    uint32_t width() const;
    uint32_t var_width() const { return var_width_; }
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
    Expr &operator&&(const Var &var) const;
    Expr &operator||(const Var &var) const;
    // slice
    virtual VarSlice &operator[](std::pair<uint32_t, uint32_t> slice);
    virtual VarSlice &operator[](uint32_t bit);
    virtual VarSlice &operator[](const std::shared_ptr<Var> &var);
    // concat
    virtual VarConcat &concat(Var &var);
    // extend
    virtual VarExtend &extend(uint32_t width);

    std::shared_ptr<Var> cast(VarCastType cast_type);

    // assignment
    std::shared_ptr<AssignStmt> assign(const std::shared_ptr<Var> &var);
    std::shared_ptr<AssignStmt> assign(Var &var);
    std::shared_ptr<AssignStmt> assign(const std::shared_ptr<Var> &var, AssignmentType type);
    std::shared_ptr<AssignStmt> assign(Var &var, AssignmentType type);
    void unassign(const std::shared_ptr<AssignStmt> &stmt);

    Generator *generator() const;
    void set_generator(Generator *gen);

    IRNode *parent() override;

    VarType type() const { return type_; }
    virtual const std::unordered_set<std::shared_ptr<AssignStmt>> &sinks() const { return sinks_; };
    virtual void remove_sink(const std::shared_ptr<AssignStmt> &stmt) { sinks_.erase(stmt); }
    virtual const std::unordered_set<std::shared_ptr<AssignStmt>> &sources() const {
        return sources_;
    };
    virtual void clear_sinks() { sinks_.clear(); }
    virtual void clear_sources() { sources_.clear(); }
    virtual void remove_source(const std::shared_ptr<AssignStmt> &stmt) { sources_.erase(stmt); }
    std::vector<std::shared_ptr<VarSlice>> &get_slices() { return slices_; }

    static void move_src_to(Var *var, Var *new_var, Generator *parent, bool keep_connection);
    static void move_sink_to(Var *var, Var *new_var, Generator *parent, bool keep_connection);
    virtual void move_linked_to(Var *new_var);
    virtual void add_sink(const std::shared_ptr<AssignStmt> &stmt) { sinks_.emplace(stmt); }
    virtual void add_source(const std::shared_ptr<AssignStmt> &stmt) { sources_.emplace(stmt); }
    void add_concat_var(const std::shared_ptr<VarConcat> &var) { concat_vars_.emplace(var); }

    template <typename T>
    std::shared_ptr<T> as() {
        return std::static_pointer_cast<T>(shared_from_this());
    }

    virtual bool inline is_struct() const { return false; }
    virtual bool inline is_packed() const { return is_packed_; }
    virtual void set_is_packed(bool value) { is_packed_ = value; }
    virtual bool inline is_enum() const { return false; }
    virtual bool inline is_function() const { return false; }
    virtual bool inline is_interface() const { return false; }
    virtual std::shared_ptr<Var> slice_var(std::shared_ptr<Var> var) { return var; }

    virtual std::string to_string() const;

    // AST stuff
    void accept(IRVisitor *visitor) override { visitor->visit(this); }
    uint64_t child_count() override;
    IRNode *get_child(uint64_t) override;

    // meta info
    // packed is only relevant when the size is larger than 1, by default it's false
    virtual std::string handle_name() const;
    virtual std::string handle_name(bool ignore_top) const;
    virtual std::string handle_name(Generator *scope) const;
    // is parametrized
    bool parametrized() const { return param_.lock() != nullptr; }
    void set_width_param(const std::shared_ptr<Param> &param);
    void set_width_param(Param *param);
    Param *param() const { return param_.lock().get(); }
    void set_explicit_array(bool value) { explicit_array_ = value; }
    bool explicit_array() const { return explicit_array_; }
    virtual std::vector<std::pair<uint32_t, uint32_t>> get_slice_index() const { return {}; }
    virtual uint32_t var_high() const { return width() - 1; }
    virtual uint32_t var_low() const { return 0; }

    [[nodiscard]] virtual std::string base_name() const { return name; }

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
    std::vector<uint32_t> size_;
    bool is_signed_;

    std::unordered_set<std::shared_ptr<AssignStmt>> sinks_;
    std::unordered_set<std::shared_ptr<AssignStmt>> sources_;

    VarType type_ = VarType::Base;

    std::unordered_set<std::shared_ptr<VarConcat>> concat_vars_;

    std::vector<std::shared_ptr<VarSlice>> slices_;

    // comment values
    std::string before_var_str_;
    std::string after_var_str_;

    // special values
    bool explicit_array_ = false;

    // parametrization
    std::weak_ptr<Param> param_;

    bool is_packed_ = false;

    std::weak_ptr<Generator> generator_;

    // assign function
    virtual std::shared_ptr<AssignStmt> assign__(const std::shared_ptr<Var> &var,
                                                 AssignmentType type);

private:
    std::unordered_map<VarCastType, std::shared_ptr<VarCasted>> casted_;
    std::unordered_map<uint32_t, std::shared_ptr<VarExtend>> extended_;
};

struct EnumType {
public:
    [[nodiscard]] virtual const Enum *enum_type() const = 0;
};

struct VarCasted : public Var, public EnumType {
public:
    VarCasted(Var *parent, VarCastType cast_type);

    void add_sink(const std::shared_ptr<AssignStmt> &stmt) override;
    void set_parent(Var *parent) { parent_var_ = parent->weak_from_this(); }

    const Var *get_var_root_parent() const override { return parent_var_.lock().get(); }

    std::string to_string() const override;

    VarCastType cast_type() const { return cast_type_; }

    // wraps all the critical functions
    // ideally this should be in another sub-class of Var and modport version as well
    // however, getting this to work with pybind with virtual inheritance is a pain
    // so just copy the code here
    const std::unordered_set<std::shared_ptr<AssignStmt>> &sinks() const override {
        return parent_var_.lock()->sinks();
    };
    void remove_sink(const std::shared_ptr<AssignStmt> &stmt) override {
        parent_var_.lock()->remove_sink(stmt);
    }
    const std::unordered_set<std::shared_ptr<AssignStmt>> &sources() const override {
        return parent_var_.lock()->sources();
    };
    void clear_sinks() override { parent_var_.lock()->clear_sources(); }
    void clear_sources() override { parent_var_.lock()->clear_sinks(); }
    void remove_source(const std::shared_ptr<AssignStmt> &stmt) override {
        parent_var_.lock()->remove_source(stmt);
    }

    void move_linked_to(Var *new_var) override { parent_var_.lock()->move_linked_to(new_var); }

    void set_enum_type(Enum *enum_);
    const Enum *enum_type() const override { return enum_type_.lock().get(); }

    bool is_enum() const override { return cast_type_ == VarCastType ::Enum; }

protected:
    std::shared_ptr<AssignStmt> assign__(const std::shared_ptr<Var> &var,
                                         AssignmentType type) override;

private:
    std::weak_ptr<Var> parent_var_;

    VarCastType cast_type_;
    // only used for enum
    std::weak_ptr<Enum> enum_type_;
};

struct VarSlice : public Var {
public:
    Var *parent_var() const { return parent_var_.lock().get(); };
    uint32_t low = 0;
    uint32_t high = 0;

    VarSlice(Var *parent, uint32_t high, uint32_t low);
    IRNode *parent() override;

    // we tie it to the parent
    void add_sink(const std::shared_ptr<AssignStmt> &stmt) override;
    void add_source(const std::shared_ptr<AssignStmt> &stmt) override;

    void set_parent(Var *parent) { parent_var_ = parent->weak_from_this(); }

    void accept(IRVisitor *visitor) override { visitor->visit(this); }

    std::string to_string() const override;

    uint32_t var_high() const override { return var_high_; }
    uint32_t var_low() const override { return var_low_; }

    std::shared_ptr<Var> slice_var(std::shared_ptr<Var> var) override {
        return var->operator[](op_).shared_from_this();
    }

    std::vector<std::pair<uint32_t, uint32_t>> get_slice_index() const override;

    const Var *get_var_root_parent() const override;
    virtual bool sliced_by_var() const { return false; }

protected:
    std::weak_ptr<Var> parent_var_;

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
    Var *sliced_var() const { return sliced_var_; }

    void accept(IRVisitor *visitor) override { visitor->visit(this); }

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
    std::string handle_name(bool) const override { return to_string(); }
    std::string handle_name(Generator *) const override { return to_string(); }

    void accept(IRVisitor *visitor) override { visitor->visit(this); }

    static Const &constant(int64_t value, uint32_t width, bool is_signed);
    Const(int64_t value, uint32_t width, bool is_signed);

    static Generator *const_gen() { return const_generator_.get(); }

    // struct is always packed
    bool is_packed() const override { return true; }
    void set_is_packed(bool value) override;

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

    const std::unordered_set<Var *> &param_vars() const { return param_vars_; }
    void add_param_var(Var *var) { param_vars_.emplace(var); }
    void set_value(int64_t new_value) override;
    void set_value(const std::shared_ptr<Param> &param);

    const Param *parent_param() const { return parent_param_; }

private:
    std::string parameter_name_;

    std::unordered_set<Var *> param_vars_;
    std::unordered_set<Param *> param_params_;
    Param *parent_param_ = nullptr;
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
    PackedSlice(PortPackedStruct *parent, const std::string &member_name);
    PackedSlice(VarPackedStruct *parent, const std::string &member_name);

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

struct VarPackedStruct : public Var, public PackedInterface {
public:
    VarPackedStruct(Generator *m, const std::string &name, PackedStruct packed_struct_);

    bool is_struct() const override { return true; }

    const PackedStruct &packed_struct() const { return struct_; }

    PackedSlice &operator[](const std::string &member_name);

    // necessary to make pybind happy due to complex inheritance
    VarSlice inline &operator[](std::pair<uint32_t, uint32_t> slice) override {
        return Var::operator[](slice);
    }
    VarSlice inline &operator[](uint32_t idx) override { return Var::operator[](idx); }

    std::set<std::string> member_names() const override;

    // struct is always packed
    bool is_packed() const override { return true; }
    void set_is_packed(bool value) override;

private:
    PackedStruct struct_;
};

struct Expr : public Var {
public:
    ExprOp op;
    Var *left;
    Var *right;

    Expr(ExprOp op, Var *left, Var *right);
    std::string to_string() const override;
    void add_sink(const std::shared_ptr<AssignStmt> &stmt) override;

    // AST
    void accept(IRVisitor *visitor) override { visitor->visit(this); }
    uint64_t child_count() override { return right ? 2 : 1; }
    IRNode *get_child(uint64_t index) override;

    std::string handle_name(bool ignore_top) const override;
    std::string handle_name(Generator *scope) const override;

protected:
    // caller is responsible for the op
    Expr(Var *left, Var *right);

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

    std::vector<Var *> &vars() { return vars_; }
    void replace_var(const std::shared_ptr<Var> &target, const std::shared_ptr<Var> &item);

    VarConcat &concat(Var &var) override;

    uint64_t child_count() override { return vars_.size(); }
    IRNode *get_child(uint64_t index) override {
        return index < vars_.size() ? vars_[index] : nullptr;
    }

    void accept(IRVisitor *visitor) override { visitor->visit(this); }

    std::string to_string() const override;
    std::string handle_name(bool ignore_top) const override;
    std::string handle_name(Generator *scope) const override;

private:
    std::vector<Var *> vars_;
};

struct VarExtend : public Expr {
public:
    VarExtend(const std::shared_ptr<Var> &var, uint32_t width);

    void add_sink(const std::shared_ptr<AssignStmt> &stmt) override;
    void add_source(const std::shared_ptr<AssignStmt> &stmt) override;
    void replace_var(const std::shared_ptr<Var> &target, const std::shared_ptr<Var> &item);

    uint64_t child_count() override { return 1; }
    IRNode *get_child(uint64_t index) override { return index == 0 ? parent_ : nullptr; }

    std::string to_string() const override;
    Var *parent_var() { return parent_; }

private:
    Var *parent_;
};

struct ConditionalExpr : public Expr {
    ConditionalExpr(const std::shared_ptr<Var> &condition, const std::shared_ptr<Var> &left,
                    const std::shared_ptr<Var> &right);
    uint64_t child_count() override { return 3; }
    IRNode *get_child(uint64_t index) override;
    void add_sink(const std::shared_ptr<AssignStmt> &stmt) override;
    std::string to_string() const override;
    std::string handle_name(bool ignore_top) const override;
    std::string handle_name(Generator *scope) const override;

    Var *condition;
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
    Enum(const std::string &name, const std::map<std::string, uint64_t> &values, uint32_t width);
    std::map<std::string, std::shared_ptr<EnumConst>> values;
    std::string name;

    uint32_t inline width() { return width_; }

    std::shared_ptr<EnumConst> get_enum(const std::string &name);
    void add_debug_info(const std::string &enum_name,
                        const std::pair<std::string, uint32_t> &debug);

    static void verify_naming_conflict(const std::map<std::string, std::shared_ptr<Enum>> &enums,
                                       const std::string &name,
                                       const std::map<std::string, uint64_t> &values);

    bool local() const { return local_; }
    bool &local() { return local_; }

private:
    uint32_t width_;
    bool local_ = true;
};

struct EnumVar : public Var, public EnumType {
public:
    bool inline is_enum() const override { return true; }

    EnumVar(Generator *m, const std::string &name, const std::shared_ptr<Enum> &enum_type)
        : Var(m, name, enum_type->width(), 1, false), enum_type_(enum_type.get()) {}

    const inline Enum *enum_type() const override { return enum_type_; }
    void accept(IRVisitor *visitor) override { visitor->visit(this); }

protected:
    std::shared_ptr<AssignStmt> assign__(const std::shared_ptr<Var> &var,
                                         AssignmentType type) override;

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

struct InterfaceVar : public Var {
public:
    InterfaceVar(InterfaceRef *interface, Generator *m, const std::string &name, uint32_t var_width,
                 const std::vector<uint32_t> &size, bool is_signed)
        : Var(m, name, var_width, size, is_signed), interface_(interface) {}

    std::string to_string() const override;

    bool inline is_interface() const override { return true; }

    std::string base_name() const override;

private:
    InterfaceRef *interface_ = nullptr;
};

// helper functions
namespace util {
std::shared_ptr<Expr> mux(Var &cond, Var &left, Var &right);
}

}  // namespace kratos
#endif  // KRATOS_EXPR_HH
