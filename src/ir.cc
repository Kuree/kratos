#include "ir.hh"

#include "cxxpool.h"
#include "generator.hh"
#include "graph.hh"
#include "util.hh"

namespace kratos {

uint64_t IRNode::index_of(kratos::IRNode *node) {
    uint64_t index;
    for (index = 0; index < child_count(); index++) {
        auto *n = get_child(index);
        if (n == node) break;
    }
    return index;
}

bool IRNode::has_attribute(const std::string &value_str) const {
    return std::any_of(attributes_.begin(), attributes_.end(),
                       [&](auto const &attr) { return attr->value_str == value_str; });
}

void IRVisitor::visit_root(IRNode *root) {
    // recursively call visits
    root->accept(this);
    level++;
    uint64_t count = 0;
    while (count < root->child_count()) {
        auto *child = root->get_child(count);
        if (visited_.find(child) == visited_.end()) {
            visited_.emplace(child);
            visit_root(child);
        }
        if (count < root->child_count() && child == root->get_child(count)) {
            count++;
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

void IRVisitor::visit_generator_root_p(kratos::Generator *generator) {
    GeneratorGraph graph(generator);
    auto levels = graph.get_leveled_generators();
    uint32_t num_cpus = get_num_cpus();
    cxxpool::thread_pool pool{num_cpus};
    for (int i = static_cast<int>(levels.size() - 1); i >= 0; i--) {
        level = static_cast<uint32_t>(i);
        pool.clear();
        auto current_level = levels[i];
        std::vector<std::future<void>> tasks;
        tasks.reserve(current_level.size());
        for (auto *mod : current_level) {
            auto t = pool.push([=](Generator *g) { g->accept_generator(this); }, mod);
            tasks.emplace_back(std::move(t));
        }
        for (auto &t : tasks) {
            t.get();
        }
    }
}

void IRVisitor::visit_content(Generator *generator) {
    generator->accept_generator(this);
    level++;
    uint64_t stmts_count = generator->stmts_count();
    for (uint64_t i = 0; i < stmts_count; i++) {
        auto *child = generator->get_child(i);
        if (visited_.find(child) == visited_.end()) {
            visited_.emplace(child);
            visit_root(child);
        }
    }
    // visit the vars
    auto var_names = generator->get_all_var_names();
    for (auto const &name : var_names) {
        auto var = generator->get_var(name);
        auto *ptr = var.get();
        if (visited_.find(ptr) == visited_.end()) {
            visited_.emplace(ptr);
            visit(var.get());
        }
    }
    // visit the functions
    // TODO: refactor this
    auto functions = generator->functions();
    for (auto const &iter : functions) {
        auto *ptr = iter.second.get();
        if (visited_.find(ptr) == visited_.end()) {
            visited_.emplace(ptr);
            visit_root(ptr);
        }
    }

    level--;
}
}  // namespace kratos