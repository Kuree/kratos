#ifndef KRATOS_AST_HH
#define KRATOS_AST_HH

#include <cstdint>
#include <vector>
#include "context.hh"

class ASTVisitor;

enum ASTNodeKind { GeneratorKind, VarKind, StmtKind };

struct ASTNode {
public:
    explicit ASTNode(ASTNodeKind type) : ast_node_type_(type) {}

    virtual void accept(ASTVisitor *) = 0;
    virtual uint64_t child_count() = 0;
    virtual ASTNode *get_child(uint64_t) = 0;

    ASTNode *ast_node() { return this; }

    virtual ASTNode *parent() { return nullptr; }
    ASTNodeKind ast_node_kind() { return ast_node_type_; }

    std::vector<std::string> f_name;
    std::vector<std::string> f_ln;

private:
    ASTNodeKind ast_node_type_;
};

class ASTVisitor {
public:
    virtual void visit_root(ASTNode *root);
    // visit generators only
    virtual void visit_generator_root(Generator *generator);

    // visit methods
    virtual inline void visit(Var *) {}
    virtual inline void visit(VarSlice *) {}
    virtual inline void visit(VarConcat *) {}
    virtual inline void visit(Expr *) {}
    virtual inline void visit(Const *) {}
    virtual inline void visit(AssignStmt *) {}
    virtual inline void visit(IfStmt *) {}
    virtual inline void visit(SwitchStmt *) {}
    virtual inline void visit(CombinationalStmtBlock *) {}
    virtual inline void visit(SequentialStmtBlock *) {}
    virtual inline void visit(ModuleInstantiationStmt *) {}

    // generator specific traversal
    virtual void visit(Generator *) {}

protected:
    uint32_t level = 0;
};

// TODO
//  implement a proper AST transformer


#endif  // KRATOS_AST_HH
