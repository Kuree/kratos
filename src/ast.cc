#include "ast.hh"

void ASTVisitor::visit(ASTNode  *root) {
    // recursively call visits
    root->accept(this);
    uint64_t child_count = root->child_count();
    for (uint64_t i = 0; i < child_count; i++) {
        visit(root->get_child(i));
    }
}