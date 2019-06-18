#ifndef DUSK_STMT_HH
#define DUSK_STMT_HH
#include "expr.hh"

enum StatementType {
    If,
    Switch,
    Assign
};

class Stmt {
public:
    Stmt(StatementType type): type_(type) {}
    StatementType type() { return type_; }
protected:
    StatementType type_;
};

class AssignmentStmt: public Stmt {
public:
    AssignmentStmt(const std::shared_ptr<Var> &left, const std::shared_ptr<Var> &right);

private:
    std::shared_ptr<Var> left = nullptr;
    std::shared_ptr<Var> right = nullptr;
};




#endif //DUSK_STMT_HH
