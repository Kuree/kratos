#ifndef KRATOS_STMT_HH
#define KRATOS_STMT_HH
#include <vector>
#include "context.hh"
#include "expr.hh"

namespace kratos {

enum StatementType { If, Switch, Assign, Block, ModuleInstantiation, FunctionalCall };
enum AssignmentType : int { Blocking, NonBlocking, Undefined };
enum StatementBlockType { Combinational, Sequential, Scope, Function };
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

protected:
    StatementType type_;
    IRNode *parent_ = nullptr;
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

    // AST stuff
    void accept(IRVisitor *visitor) override { visitor->visit(this); }
    uint64_t child_count() override { return 2; }
    IRNode *get_child(uint64_t index) override;

private:
    std::shared_ptr<Var> left_ = nullptr;
    std::shared_ptr<Var> right_ = nullptr;

    AssignmentType assign_type_;
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

private:
    std::shared_ptr<Var> target_;
    // default case will be indexed as nullptr
    std::map<std::shared_ptr<Const>, std::shared_ptr<ScopedStmtBlock>> body_;
};

/// this is for always block
class StmtBlock : public Stmt {
public:
    StatementBlockType block_type() const { return block_type_; }
    void add_stmt(const std::shared_ptr<Stmt> &stmt);
    void add_stmt(Stmt &stmt) { add_stmt(stmt.shared_from_this()); }
    void remove_stmt(const std::shared_ptr<Stmt> &stmt);

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
    FunctionStmtBlock(Generator *parent, std::string function_name)
        : StmtBlock(StatementBlockType::Function),
          parent_(parent),
          function_name_(std::move(function_name)) {}

    std::shared_ptr<Port> input(const std::string &name, uint32_t width, bool is_signed);
    const std::map<std::string, std::shared_ptr<Port>> &ports() const { return ports_; }
    std::shared_ptr<Port> get_port(const std::string &port_name);
    void return_(const std::shared_ptr<Var> &expr) { return_value_  = expr; }
    std::shared_ptr<Var> return_value() { return return_value_; }
    std::string function_name() { return function_name_; }

    void set_parent(IRNode *parent) override;

    void accept(IRVisitor *visitor) override { visitor->visit(this); }

private:
    Generator *parent_;
    std::string function_name_;

    std::map<std::string, std::shared_ptr<Port>> ports_;
    std::shared_ptr<Var> return_value_ = nullptr;
};

class FunctionCallStmt : public Stmt {
public:
    FunctionCallStmt(const std::shared_ptr<FunctionStmtBlock> &func,
                     const std::map<std::string, std::shared_ptr<Var>> &args);

    const std::shared_ptr<FunctionStmtBlock> &func() { return func_; }
    const std::map<std::string, std::shared_ptr<Var>> &args() const { return args_; };

    void accept(IRVisitor *visitor) override { visitor->visit(this); }

private:
    std::shared_ptr<FunctionStmtBlock> func_;
    std::map<std::string, std::shared_ptr<Var>> args_;
};

class ModuleInstantiationStmt : public Stmt {
public:
    ModuleInstantiationStmt(Generator *target, Generator *parent);

    void accept(IRVisitor *visitor) override { visitor->visit(this); }

    const std::map<std::shared_ptr<Var>, std::shared_ptr<Var>> &port_mapping() const {
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
    std::map<std::shared_ptr<Var>, std::shared_ptr<Var>> port_mapping_;

    std::map<std::shared_ptr<Var>, std::shared_ptr<Stmt>> port_debug_;
};

}  // namespace kratos

#endif  // KRATOS_STMT_HH
