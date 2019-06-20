#ifndef DUSK_STMT_HH
#define DUSK_STMT_HH
#include "context.hh"
#include "expr.hh"

enum StatementType { If, Switch, Assign, Block };
enum AssignmentType : int { Blocking, NonBlocking, Undefined };
enum StatementBlockType { Combinational, Sequential };
enum BlockEdgeType { Posedge, Negedge };

class StmtBlock;

class Stmt : public std::enable_shared_from_this<Stmt> {
public:
    explicit Stmt(StatementType type) : type_(type) {}
    StatementType type() { return type_; }
    template <typename T>
    std::shared_ptr<T> as() {
        return std::static_pointer_cast<T>(shared_from_this());
    }

protected:
    StatementType type_;
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

    bool equal(const std::shared_ptr<AssignStmt> &stmt) const;
    bool operator==(const AssignStmt &stmt) const;

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

    const std::shared_ptr<Var> target() const { return target_; }

    const std::map<std::shared_ptr<Const>, std::shared_ptr<Stmt>> &body() const { return body_; }

private:
    std::shared_ptr<Var> target_;
    std::map<std::shared_ptr<Const>, std::shared_ptr<Stmt>> body_;
};

/// this is for always block
class StmtBlock : public Stmt {
public:
    StatementBlockType block_type() const { return block_type_; }
    void add_statement(std::shared_ptr<Stmt> stmt);
    void add_statement(Stmt &stmt) { add_statement(stmt.shared_from_this()); }

protected:
    explicit StmtBlock(StatementBlockType type);

private:
    StatementBlockType block_type_;
    std::vector<std::shared_ptr<Stmt>> stmts_;
};

class CombinationalStmtBlock : public StmtBlock {
public:
    CombinationalStmtBlock() : StmtBlock(StatementBlockType::Combinational) {}
};

class SequentialStmtBlock : public StmtBlock {
public:
    SequentialStmtBlock() : StmtBlock(StatementBlockType::Sequential) {}

    const std::set<std::pair<BlockEdgeType, std::shared_ptr<Var>>> &get_conditions() const {
        return conditions_;
    }

    void add_condition(const std::pair<BlockEdgeType, std::shared_ptr<Var>> &condition);

private:
    std::set<std::pair<BlockEdgeType, std::shared_ptr<Var>>> conditions_;
};
#endif  // DUSK_STMT_HH
