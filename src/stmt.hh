#ifndef DUSK_STMT_HH
#define DUSK_STMT_HH
#include "context.hh"
#include "expr.hh"

enum StatementType { If, Switch, Assign, Block };
enum AssignmentType : int { Blocking, NonBlocking, Undefined };
enum StatementBlockType { Combinational, Sequential };

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

    AssignmentType assign_type() { return assign_type_; }

    const std::shared_ptr<Var> left() const { return left_; }
    const std::shared_ptr<Var> right() const { return right_; }

private:
    std::shared_ptr<Var> left_ = nullptr;
    std::shared_ptr<Var> right_ = nullptr;

    AssignmentType assign_type_;
};

class IfStmt : public Stmt {
public:
    IfStmt(std::shared_ptr<Var> predicate);

    const std::shared_ptr<Var> predicate() const { return predicate_; }
    const std::vector<std::shared_ptr<Stmt>> then_body() const { return then_body_; }
    const std::vector<std::shared_ptr<Stmt>> else_body() const { return else_body_; }
    void add_then_stmt(const std::shared_ptr<Stmt> &stmt);
    void add_else_stmt(const std::shared_ptr<Stmt> &stmt);

private:
    std::shared_ptr<Var> predicate_;
    std::vector<std::shared_ptr<Stmt>> then_body_;
    std::vector<std::shared_ptr<Stmt>> else_body_;
};

class SwitchStmt : public Stmt {
    SwitchStmt();

private:
};

/// this is for always block
class StmtBlock : public Stmt {
public:
    explicit StmtBlock(StatementBlockType type);
    StatementBlockType block_type() const { return block_type_; }
    void add_statement(const std::shared_ptr<Stmt> &stmt);

private:
    StatementBlockType block_type_;
    std::vector<std::shared_ptr<Stmt>> stmts_;
};

#endif  // DUSK_STMT_HH
