#include "ir.hh"
#include "generator.hh"

namespace kratos {
void IRVisitor::visit_root(IRNode *root) {
    // recursively call visits
    root->accept(this);
    uint64_t child_count = root->child_count();
    level++;
    for (uint64_t i = 0; i < child_count; i++) {
        auto child = root->get_child(i);
        if (visited_.find(child) == visited_.end()) {
            visited_.emplace(child);
            visit_root(child);
        }
    }
    level--;
}

void IRVisitor::visit_generator_root(Generator *generator) {
    auto children = generator->get_child_generators();
    generator->accept_generator(this);
    level++;
    for (auto &child : children) visit_generator_root(child.get());
    level--;
}

void IRVisitor::visit_content(Generator *generator) {
    generator->accept_generator(this);
    level++;
    uint64_t stmts_count = generator->stmts_count();
    for (uint64_t i = 0; i < stmts_count; i++) {
        auto child = generator->get_child(i);
        if (visited_.find(child) == visited_.end()) {
            visited_.emplace(child);
            visit_root(child);
        }
    }
    // visit the vars
    auto var_names = generator->get_all_var_names();
    for (auto const &name : var_names) {
        auto var = generator->get_var(name);
        auto ptr = var.get();
        if (visited_.find(ptr) == visited_.end()) {
            visited_.emplace(ptr);
            visit(var.get());
        }
    }
    level--;
}
}