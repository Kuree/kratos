#ifndef DUSK_STMT_HH
#define DUSK_STMT_HH
#include "context.hh"
#include "expr.hh"

enum StatementType { If, Switch, Assign };
enum AssignmentType : int { Blocking, NonBlocking, Undefined };

class Stmt: public std::enable_shared_from_this<Stmt> {
public:
    explicit Stmt(StatementType type) : type_(type) {}
    StatementType type() { return type_; }

protected:
    StatementType type_;
};

class AssignStmt : public Stmt {
public:
    AssignStmt(std::shared_ptr<Var> left, std::shared_ptr<Var> right);
    AssignStmt(std::shared_ptr<Var> left, std::shared_ptr<Var> right, AssignmentType type);

    AssignmentType assign_type() { return assign_type_; }

    const std::shared_ptr<Var> left() const { return left_; }
    const std::shared_ptr<Var> right() const { return right_; }

private:
    std::shared_ptr<Var> left_ = nullptr;
    std::shared_ptr<Var> right_ = nullptr;

    AssignmentType assign_type_;
};

#endif  // DUSK_STMT_HH
