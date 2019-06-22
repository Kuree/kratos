#ifndef DUSK_PASS_HH
#define DUSK_PASS_HH

#include "ast.hh"
#include "context.hh"
#include "stmt.hh"

class AssignmentTypeVisitor : public ASTVisitor {
public:
    explicit AssignmentTypeVisitor(AssignmentType type, bool check_type = true)
        : ASTVisitor(), type_(type), check_type_(check_type) {}
    void visit(AssignStmt* stmt) override;

private:
    AssignmentType type_;
    bool check_type_;
};

class AssignmentTypeBlockVisitor : public ASTVisitor {
    void visit(CombinationalStmtBlock* block) override;
    void visit(SequentialStmtBlock* block) override ;
};

void fix_assignment_type(Generator* generator);

#endif  // DUSK_PASS_HH
