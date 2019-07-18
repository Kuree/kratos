#ifndef KRATOS_STMT_HH
#define KRATOS_STMT_HH
#include <vector>
#include "context.hh"
#include "expr.hh"

enum StatementType { If, Switch, Assign, Block, ModuleInstantiation };
enum AssignmentType : int { Blocking, NonBlocking, Undefined };
enum StatementBlockType { Combinational, Sequential };
enum BlockEdgeType { Posedge, Negedge };

class StmtBlock;

class Stmt : public std::enable_shared_from_this<Stmt>, public ASTNode {
public:
    explicit Stmt(StatementType type) : ASTNode(ASTNodeKind::StmtKind), type_(type) {}
    StatementType type() { return type_; }
    template <typename T>
    std::shared_ptr<T> as() {
        return std::static_pointer_cast<T>(shared_from_this());
    }

    ASTNode *parent() override;
    virtual void set_parent(ASTNode *parent) { parent_ = parent; }

    void accept(ASTVisitor *) override {}
    uint64_t child_count() override { return 0; }
    ASTNode *get_child(uint64_t) override { return nullptr; };

protected:
    StatementType type_;
    ASTNode *parent_ = nullptr;
};

class AssignStmt : public Stmt {
public:
    AssignStmt(const std::shared_ptr<Var> &left, const std::shared_ptr<Var> &right);
    AssignStmt(const std::shared_ptr<Var> &left, const std::shared_ptr<Var> &right,
               AssignmentType type);

    AssignmentType assign_type() const { return assign_type_; }
    void set_assign_type(AssignmentType assign_type) { assign_type_ = assign_type; }

    const std::shared_ptr<Var> left() const { return left_; }
    const std::shared_ptr<Var> right() const { return right_; }

    void set_left(const std::shared_ptr<Var> &left) { left_ = left; }
    void set_right(const std::shared_ptr<Var> &right) { right_ = right; }

    bool equal(const std::shared_ptr<AssignStmt> &stmt) const;
    bool operator==(const AssignStmt &stmt) const;

    // AST stuff
    void accept(ASTVisitor *visitor) override { visitor->visit(this); }
    uint64_t child_count() override { return 2; }
    ASTNode *get_child(uint64_t index) override;

private:
    std::shared_ptr<Var> left_ = nullptr;
    std::shared_ptr<Var> right_ = nullptr;

    AssignmentType assign_type_;
};

class IfStmt : public Stmt {
public:
    explicit IfStmt(std::shared_ptr<Var> predicate);
    explicit IfStmt(Var &var) : IfStmt(var.shared_from_this()) {}

    const std::shared_ptr<Var> predicate() const { return predicate_; }
    const std::vector<std::shared_ptr<Stmt>> then_body() const { return then_body_; }
    const std::vector<std::shared_ptr<Stmt>> else_body() const { return else_body_; }
    void add_then_stmt(const std::shared_ptr<Stmt> &stmt);
    void add_then_stmt(Stmt &stmt) { add_then_stmt(stmt.shared_from_this()); }
    void add_else_stmt(const std::shared_ptr<Stmt> &stmt);
    void add_else_stmt(Stmt &stmt) { add_else_stmt(stmt.shared_from_this()); }

    // AST stuff
    void accept(ASTVisitor *visitor) override { visitor->visit(this); }
    uint64_t child_count() override { return 1 + then_body_.size() + else_body_.size(); }
    ASTNode *get_child(uint64_t index) override;

private:
    std::shared_ptr<Var> predicate_;
    std::vector<std::shared_ptr<Stmt>> then_body_;
    std::vector<std::shared_ptr<Stmt>> else_body_;
};

class SwitchStmt : public Stmt {
public:
    explicit SwitchStmt(const std::shared_ptr<Var> &target);

    void add_switch_case(const std::shared_ptr<Const> &switch_case,
                         const std::shared_ptr<Stmt> &stmt);

    void add_switch_case(const std::shared_ptr<Const> &switch_case,
                         const std::vector<std::shared_ptr<Stmt>> &stmts);

    const std::shared_ptr<Var> target() const { return target_; }

    const std::map<std::shared_ptr<Const>, std::vector<std::shared_ptr<Stmt>>> &body() const {
        return body_;
    }

    // AST stuff
    void accept(ASTVisitor *visitor) override { visitor->visit(this); }
    uint64_t child_count() override;
    ASTNode *get_child(uint64_t index) override;

private:
    std::shared_ptr<Var> target_;
    // default case will be indexed as nullptr
    std::map<std::shared_ptr<Const>, std::vector<std::shared_ptr<Stmt>>> body_;
};

/// this is for always block
class StmtBlock : public Stmt {
public:
    StatementBlockType block_type() const { return block_type_; }
    void add_statement(const std::shared_ptr<Stmt> &stmt);
    void add_statement(Stmt &stmt) { add_statement(stmt.shared_from_this()); }

    uint64_t child_count() override { return stmts_.size(); }
    ASTNode *get_child(uint64_t index) override {
        return index < stmts_.size() ? stmts_[index].get() : nullptr;
    }

    void set_child(uint64_t index, const std::shared_ptr<Stmt> &stmt);

protected:
    explicit StmtBlock(StatementBlockType type);
    std::vector<std::shared_ptr<Stmt>> stmts_;

private:
    StatementBlockType block_type_;
};

class CombinationalStmtBlock : public StmtBlock {
public:
    CombinationalStmtBlock() : StmtBlock(StatementBlockType::Combinational) {}

    // AST stuff
    void accept(ASTVisitor *visitor) override { visitor->visit(this); }
};

class SequentialStmtBlock : public StmtBlock {
public:
    SequentialStmtBlock() : StmtBlock(StatementBlockType::Sequential) {}

    const std::set<std::pair<BlockEdgeType, std::shared_ptr<Var>>> &get_conditions() const {
        return conditions_;
    }

    void add_condition(const std::pair<BlockEdgeType, std::shared_ptr<Var>> &condition);

    void accept(ASTVisitor *visitor) override { visitor->visit(this); }

private:
    std::set<std::pair<BlockEdgeType, std::shared_ptr<Var>>> conditions_;
};

class ModuleInstantiationStmt : public Stmt {
public:
    ModuleInstantiationStmt(Generator *target, Generator *parent);

    void accept(ASTVisitor *visitor) override { visitor->visit(this); }

    const std::map<std::shared_ptr<Var>, std::shared_ptr<Var>> &port_mapping() const {
        return port_mapping_;
    }

    const std::map<std::shared_ptr<Var>, std::shared_ptr<Stmt>> port_debug() const {
        return port_debug_;
    }

    const Generator *target() { return target_; }

private:
    Generator *target_;
    Generator *parent_;
    std::map<std::shared_ptr<Var>, std::shared_ptr<Var>> port_mapping_;

    std::map<std::shared_ptr<Var>, std::shared_ptr<Stmt>> port_debug_;
};
#endif  // KRATOS_STMT_HH
