#ifndef DUSK_AST_HH
#define DUSK_AST_HH

#include <cstdint>
#include "context.hh"

class ASTVisitor;

struct ASTNode {
public:
    virtual void accept(ASTVisitor *) = 0;
    virtual uint64_t child_count() = 0;
    virtual ASTNode *get_child(uint64_t) = 0;

    ASTNode *ast_node() { return this; }
};

class ASTVisitor {
public:
    void visit_root(ASTNode *root);

    // visit methods
    virtual void visit(Generator *) {}
    virtual void visit(Var *) {}
    virtual void visit(VarSlice *) {}
    virtual void visit(Expr *) {}
    virtual void visit(Const *) {}
    virtual void visit(AssignStmt *) {}
    virtual void visit(IfStmt *) {}
    virtual void visit(SwitchStmt *) {}
    virtual void visit(CombinationalStmtBlock *) {}
    virtual void visit(SequentialStmtBlock *) {}
};

#endif  // DUSK_AST_HH
