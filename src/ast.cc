#include "ast.hh"
#include "generator.hh"

void ASTVisitor::visit_root(ASTNode *root) {
    // recursively call visits
    root->accept(this);
    uint64_t child_count = root->child_count();
    for (uint64_t i = 0; i < child_count; i++) {
        visit_root(root->get_child(i));
    }
}

void ASTVisitor::visit_generator_root(Generator* generator) {
    auto &children = generator->get_child_generators();
    generator->accept_generator(this);
    for (auto &child: children)
        visit_generator_root(child.get());
}