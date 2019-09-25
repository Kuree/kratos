#ifndef KRATOS_STMT_HH
#define KRATOS_STMT_HH
#include <vector>
#include "context.hh"
#include "expr.hh"

namespace kratos {

enum StatementType {
    If,
    Switch,
    Assign,
    Block,
    ModuleInstantiation,
    FunctionalCall,
    Return,
    Assert
};

enum AssignmentType : int { Blocking, NonBlocking, Undefined };
enum StatementBlockType { Combinational, Sequential, Scope, Function, Initial };
enum BlockEdgeType { Posedge, Negedge };

class StmtBlock;
class ScopedStmtBlock;

class Stmt : public std::enable_shared_from_this<Stmt>, public IRNode {
public:
    explicit Stmt(StatementType type) : IRNode(IRNodeKind::StmtKind), type_(type) {}
    StatementType type() { return type_; }
    template <typename T>
    std::shared_ptr<T> as() {
        return std::static_pointer_cast<T>(shared_from_this());
    }

    IRNode *parent() override;
    virtual void set_parent(IRNode *parent) { parent_ = parent; }
    Generator *generator_parent() const;

    void accept(IRVisitor *) override {}
    uint64_t child_count() override { return 0; }
    IRNode *get_child(uint64_t) override { return nullptr; };

    ~Stmt() override = default;

    // debug
    int stmt_id() const { return stmt_id_; }
    void set_stmt_id(uint32_t id) { stmt_id_ = id; }
    const std::map<std::string, std::pair<bool, std::string>> &scope_context() const {
        return scope_context_;
    }
    // For now it's a flat context that every breakpoint/stmt has its own context
    // in the future if the performance/storage size is a concern, we can group the stmt
    // together
    virtual void add_scope_variable(const std::string &name, const std::string &value, bool is_var,
                                    bool override);

protected:
    StatementType type_;
    IRNode *parent_ = nullptr;
    int stmt_id_ = -1;

    std::map<std::string, std::pair<bool, std::string>> scope_context_;
};

class AssignStmt : public Stmt {
public:
    AssignStmt(const std::shared_ptr<Var> &left, const std::shared_ptr<Var> &right);
    AssignStmt(const std::shared_ptr<Var> &left, const std::shared_ptr<Var> &right,
               AssignmentType type);

    AssignmentType assign_type() const { return assign_type_; }
    void set_assign_type(AssignmentType assign_type) { assign_type_ = assign_type; }

    std::shared_ptr<Var> left() const { return left_; }
    std::shared_ptr<Var> right() const { return right_; }
    std::shared_ptr<Var> &left() { return left_; }
    std::shared_ptr<Var> &right() { return right_; }

    void set_left(const std::shared_ptr<Var> &left) { left_ = left; }
    void set_right(const std::shared_ptr<Var> &right) { right_ = right; }

    void set_parent(IRNode *parent) override;

    bool equal(const std::shared_ptr<AssignStmt> &stmt) const;
    bool operator==(const AssignStmt &stmt) const;

    // delay. this is only used during test bench generation
    int inline get_delay() const { return delay_; }
    void set_delay(int delay) { delay_ = delay; }

    // AST stuff
    void accept(IRVisitor *visitor) override { visitor->visit(this); }
    uint64_t child_count() override { return 2; }
    IRNode *get_child(uint64_t index) override;

private:
    std::shared_ptr<Var> left_ = nullptr;
    std::shared_ptr<Var> right_ = nullptr;

    AssignmentType assign_type_;

    int delay_ = -1;
};

class IfStmt : public Stmt {
public:
    explicit IfStmt(std::shared_ptr<Var> predicate);
    explicit IfStmt(Var &var) : IfStmt(var.shared_from_this()) {}

    std::shared_ptr<Var> predicate() const { return predicate_; }
    const std::shared_ptr<ScopedStmtBlock> &then_body() const { return then_body_; }
    const std::shared_ptr<ScopedStmtBlock> &else_body() const { return else_body_; }
    void add_then_stmt(const std::shared_ptr<Stmt> &stmt);
    void add_then_stmt(Stmt &stmt) { add_then_stmt(stmt.shared_from_this()); }
    void add_else_stmt(const std::shared_ptr<Stmt> &stmt);
    void add_else_stmt(Stmt &stmt) { add_else_stmt(stmt.shared_from_this()); }
    void remove_then_stmt(const std::shared_ptr<Stmt> &stmt);
    void remove_else_stmt(const std::shared_ptr<Stmt> &stmt);
    void remove_stmt(const std::shared_ptr<Stmt> &stmt);

    // AST stuff
    void accept(IRVisitor *visitor) override { visitor->visit(this); }
    uint64_t child_count() override { return 3; }
    IRNode *get_child(uint64_t index) override;

    // Debug
    void add_scope_variable(const std::string &name, const std::string &value, bool is_var,
                            bool override) override;

private:
    std::shared_ptr<Var> predicate_;
    std::shared_ptr<ScopedStmtBlock> then_body_;
    std::shared_ptr<ScopedStmtBlock> else_body_;
};

class SwitchStmt : public Stmt {
public:
    explicit SwitchStmt(const std::shared_ptr<Var> &target);

    ScopedStmtBlock &add_switch_case(const std::shared_ptr<Const> &switch_case,
                                     const std::shared_ptr<Stmt> &stmt);

    ScopedStmtBlock &add_switch_case(const std::shared_ptr<Const> &switch_case,
                                     const std::vector<std::shared_ptr<Stmt>> &stmts);

    void remove_switch_case(const std::shared_ptr<Const> &switch_case);
    void remove_switch_case(const std::shared_ptr<Const> &switch_case,
                            const std::shared_ptr<Stmt> &stmt);
    void remove_stmt(const std::shared_ptr<Stmt> &stmt);

    std::shared_ptr<Var> target() const { return target_; }

    const std::map<std::shared_ptr<Const>, std::shared_ptr<ScopedStmtBlock>> &body() const {
        return body_;
    }

    // AST stuff
    void accept(IRVisitor *visitor) override { visitor->visit(this); }
    uint64_t child_count() override { return body_.size() + 1; }
    IRNode *get_child(uint64_t index) override;

    // Debug
    void add_scope_variable(const std::string &name, const std::string &value, bool is_var,
                            bool override) override;

private:
    std::shared_ptr<Var> target_;
    // default case will be indexed as nullptr
    std::map<std::shared_ptr<Const>, std::shared_ptr<ScopedStmtBlock>> body_;
};

class StmtBlock : public Stmt {
public:
    StatementBlockType block_type() const { return block_type_; }
    void add_stmt(const std::shared_ptr<Stmt> &stmt);
    void add_stmt(Stmt &stmt) { add_stmt(stmt.shared_from_this()); }
    void remove_stmt(const std::shared_ptr<Stmt> &stmt);
    void inline clear() { stmts_.clear(); }

    uint64_t child_count() override { return stmts_.size(); }
    IRNode *get_child(uint64_t index) override {
        return index < stmts_.size() ? stmts_[index].get() : nullptr;
    }

    void set_child(uint64_t index, const std::shared_ptr<Stmt> &stmt);

    std::vector<std::shared_ptr<Stmt>>::iterator begin() { return stmts_.begin(); }
    std::vector<std::shared_ptr<Stmt>>::iterator end() { return stmts_.end(); }
    std::shared_ptr<Stmt> back() { return stmts_.back(); }
    bool empty() const { return stmts_.empty(); }
    uint64_t size() const { return stmts_.size(); }
    std::shared_ptr<Stmt> operator[](uint32_t index) { return stmts_[index]; }
    void set_stmts(const std::vector<std::shared_ptr<Stmt>> &stmts) { stmts_ = stmts; }

    // Debug
    void add_scope_variable(const std::string &name, const std::string &value, bool is_var,
                            bool override) override;

protected:
    explicit StmtBlock(StatementBlockType type);
    std::vector<std::shared_ptr<Stmt>> stmts_;

private:
    StatementBlockType block_type_;
};

class ScopedStmtBlock : public StmtBlock {
public:
    ScopedStmtBlock() : StmtBlock(StatementBlockType::Scope) {}
    void accept(IRVisitor *visitor) override { visitor->visit(this); }
};

class CombinationalStmtBlock : public StmtBlock {
public:
    CombinationalStmtBlock() : StmtBlock(StatementBlockType::Combinational) {}

    // AST stuff
    void accept(IRVisitor *visitor) override { visitor->visit(this); }
};

class SequentialStmtBlock : public StmtBlock {
public:
    SequentialStmtBlock() : StmtBlock(StatementBlockType::Sequential) {}

    const std::vector<std::pair<BlockEdgeType, std::shared_ptr<Var>>> &get_conditions() const {
        return conditions_;
    }

    void add_condition(const std::pair<BlockEdgeType, std::shared_ptr<Var>> &condition);

    void accept(IRVisitor *visitor) override { visitor->visit(this); }

private:
    std::vector<std::pair<BlockEdgeType, std::shared_ptr<Var>>> conditions_;
};

class FunctionStmtBlock : public StmtBlock {
public:
    FunctionStmtBlock(Generator *parent, std::string function_name);

    virtual std::shared_ptr<Port> input(const std::string &name, uint32_t width, bool is_signed);
    const std::map<std::string, std::shared_ptr<Port>> &ports() const { return ports_; }
    std::shared_ptr<Port> get_port(const std::string &port_name);
    bool has_return_value() const { return has_return_value_; }
    void set_has_return_value(bool value) { has_return_value_ = value; }
    std::string function_name() const { return function_name_; }
    std::shared_ptr<Var> function_handler() { return function_handler_; };
    void create_function_handler(uint32_t width, bool is_signed);
    std::shared_ptr<ReturnStmt> return_stmt(const std::shared_ptr<Var> &var);
    void set_port_ordering(const std::map<std::string, uint32_t> &ordering);
    void set_port_ordering(const std::map<uint32_t, std::string> &ordering);
    const std::map<std::string, uint32_t> &port_ordering() const { return port_ordering_; }
    Generator *generator() { return parent_; }

    void accept(IRVisitor *visitor) override { visitor->visit(this); }

    // to distinguish from dpi function
    virtual bool is_dpi() { return false; }

protected:
    Generator *parent_;
    std::string function_name_;

    std::map<std::string, std::shared_ptr<Port>> ports_;
    bool has_return_value_ = false;
    std::shared_ptr<Var> function_handler_ = nullptr;
    std::map<std::string, uint32_t> port_ordering_;
};

class InitialStmtBlock : public StmtBlock {
public:
    InitialStmtBlock() : StmtBlock(StatementBlockType::Initial) {}

    void accept(IRVisitor *visitor) override { visitor->visit(this); }
};

class DPIFunctionStmtBlock : public FunctionStmtBlock {
public:
    DPIFunctionStmtBlock(Generator *parent, const std::string &function_name)
        : FunctionStmtBlock(parent, function_name) {}
    std::shared_ptr<Port> output(const std::string &name, uint32_t width, bool is_signed);
    std::shared_ptr<Port> input(const std::string &name, uint32_t width, bool is_signed) override;

    uint32_t return_width() { return return_width_; }
    void set_return_width(uint32_t value) { return_width_ = value; }

    bool is_dpi() override { return true; }
    bool is_context() const { return is_context_; }
    bool is_pure() const { return is_pure_; }
    void set_is_context(bool value);
    void set_is_pure(bool value);

protected:
    uint32_t return_width_ = 0;
    bool is_context_ = false;
    bool is_pure_ = false;
};

class ReturnStmt : public Stmt {
public:
    ReturnStmt(FunctionStmtBlock *func_def, std::shared_ptr<Var> value);
    void set_parent(IRNode *parent) override;

    void accept(IRVisitor *visitor) override { visitor->visit(this); }

    const FunctionStmtBlock *func_def() const { return func_def_; }
    std::shared_ptr<Var> value() const { return value_; }

private:
    FunctionStmtBlock *func_def_;
    std::shared_ptr<Var> value_;
};

class FunctionCallStmt : public Stmt {
public:
    FunctionCallStmt(const std::shared_ptr<FunctionStmtBlock> &func,
                     const std::map<std::string, std::shared_ptr<Var>> &args);

    explicit FunctionCallStmt(const std::shared_ptr<FunctionCallVar> &var);

    const std::shared_ptr<FunctionStmtBlock> &func() { return func_; }
    const std::shared_ptr<FunctionCallVar> &var() const { return var_; };

    void accept(IRVisitor *visitor) override { visitor->visit(this); }

private:
    std::shared_ptr<FunctionStmtBlock> func_;
    std::shared_ptr<FunctionCallVar> var_;
};

class ModuleInstantiationStmt : public Stmt {
public:
    ModuleInstantiationStmt(Generator *target, Generator *parent);

    void accept(IRVisitor *visitor) override { visitor->visit(this); }

    const std::map<std::shared_ptr<Port>, std::shared_ptr<Var>> &port_mapping() const {
        return port_mapping_;
    }

    const std::map<std::shared_ptr<Var>, std::shared_ptr<Stmt>> &port_debug() const {
        return port_debug_;
    }

    const Generator *target() { return target_; }
    const Generator *module_parent() { return parent_; }

private:
    Generator *target_;
    Generator *parent_;
    std::map<std::shared_ptr<Port>, std::shared_ptr<Var>> port_mapping_;

    std::map<std::shared_ptr<Var>, std::shared_ptr<Stmt>> port_debug_;
};

}  // namespace kratos

#endif  // KRATOS_STMT_HH
