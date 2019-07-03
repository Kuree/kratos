#include "ast.hh"
#include "generator.hh"

void ASTVisitor::visit_root(ASTNode *root) {
    // recursively call visits
    root->accept(this);
    uint64_t child_count = root->child_count();
    level++;
    for (uint64_t i = 0; i < child_count; i++) {
        visit_root(root->get_child(i));
    }
    level--;
}

void ASTVisitor::visit_generator_root(Generator *generator) {
    auto &children = generator->get_child_generators();
    generator->accept_generator(this);
    level++;
    for (auto &child : children) visit_generator_root(child.get());
    level--;
}

void ASTVisitor::visit_content(Generator *generator) {
    generator->accept_generator(this);
    level++;
    uint64_t child_count = generator->child_count();
    for (uint64_t i = 0; i < child_count; i++) {
        auto child = generator->get_child(i);
        if (child->ast_node_kind() != ASTNodeKind ::GeneratorKind)
            visit_root(generator->get_child(i));
    }
    // visit the vars
    auto var_names = generator->get_all_var_names();
    for (auto const &name: var_names) {
        auto var = generator->get_var(name);
        visit(var.get());
    }
    level--;
}