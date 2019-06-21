#ifndef DUSK_AST_HH
#define DUSK_AST_HH

#include <cstdint>

class ASTVisitor;

struct ASTNode {
public:
    virtual void accept(ASTVisitor *) = 0;
    virtual uint64_t child_count() = 0;
    virtual ASTNode *get_child(uint64_t) = 0;
};

class ASTVisitor {
public:
    template <typename T>
    void visit(T *) {}

    void visit(ASTNode *root);
};

#endif  // DUSK_AST_HH
