#include "graph.hh"
#include <unordered_set>
#include "ast.hh"
#include "fmt/format.h"
#include "generator.hh"

using fmt::format;

class GeneratorVisitor : public ASTVisitor {
public:
    explicit GeneratorVisitor(GeneratorGraph *g) : g_(g) {}
    void visit(Generator *generator) override { g_->add_node(generator); }

private:
    GeneratorGraph *g_;
};

class GeneratorGraphVisitor : public ASTVisitor {
public:
    explicit GeneratorGraphVisitor(GeneratorGraph *g) : g_(g) {}
    void visit(Generator *generator) override {
        auto parent_node = g_->get_node(generator);
        for (auto const &child : generator->get_child_generators()) {
            auto child_node = g_->get_node(child.get());
            if (child_node->parent != nullptr)
                throw std::runtime_error(::format("{0} already has a parent",
                                                  child_node->parent->generator->instance_name));
            child_node->parent = parent_node;
            parent_node->children.emplace(child_node->generator);
        }
    }

private:
    GeneratorGraph *g_;
};

GeneratorGraph::GeneratorGraph(Generator *generator) : root_(generator) {
    // first pass create nodes for each generator
    GeneratorVisitor visitor(this);
    visitor.visit_generator_root(generator);
    // second pass to build the graph
    GeneratorGraphVisitor g_visitor(this);
    g_visitor.visit_generator_root(generator);
}

GeneratorNode *GeneratorGraph::add_node(Generator *generator) {
    if (nodes_.find(generator) != nodes_.end()) {
        throw std::runtime_error(
            ::format("{0} was used in another generator!", generator->instance_name));
    }
    GeneratorNode node;
    node.generator = generator;
    nodes_.emplace(generator, node);
    // return the pointer hosted by the nodes_
    return &nodes_.at(generator);
}

GeneratorNode *GeneratorGraph::get_node(Generator *generator) {
    if (nodes_.find(generator) == nodes_.end()) {
        throw std::runtime_error(::format("{0} not found in graph!", generator->instance_name));
    }
    return &nodes_.at(generator);
}

void topological_sort_helper(GeneratorGraph *g, GeneratorNode *node,
                             std::unordered_set<GeneratorNode *> &visited,
                             std::queue<GeneratorNode *> &queue) {
    // mark it as visited
    visited.emplace(node);

    // visit all the child node
    for (auto &child : node->children) {
        auto child_node = g->get_node(child);
        if (visited.find(child_node) == visited.end()) {
            // visit it
            topological_sort_helper(g, child_node, visited, queue);
        }
    }
    queue.push(node);
}

std::queue<GeneratorNode *> GeneratorGraph::topological_sort() {
    std::unordered_set<GeneratorNode *> visited;
    std::queue<GeneratorNode *> queue;
    for (auto &iter : nodes_) {
        auto node = &iter.second;
        if (visited.find(node) == visited.end()) {
            // visit it
            topological_sort_helper(this, node, visited, queue);
        }
    }
    return queue;
}

std::vector<Generator *> GeneratorGraph::get_sorted_generators() {
    auto queue = topological_sort();
    std::vector<Generator *> result;
    result.reserve(queue.size());
    while (!queue.empty()) {
        result.emplace_back(queue.front()->generator);
        queue.pop();
    }
    return result;
}

std::vector<std::unordered_set<Generator *>> GeneratorGraph::get_leveled_generators() {
    // this is a modified breath-first search
    std::queue<std::pair<Generator *, uint32_t>> queue;
    std::unordered_map<GeneratorNode *, uint32_t> level_index;

    queue.push({root_, 0});
    uint32_t max_level = 0;

    while (!queue.empty()) {
        const auto &[generator, current_level] = queue.front();
        queue.pop();
        auto const &node = get_node(generator);
        if (level_index.find(node) == level_index.end() || level_index.at(node) < current_level) {
            // update the new level
            level_index[node] = current_level;
        }
        // loop through all the child generators
        for (const auto &child_generator : generator->get_child_generators()) {
            queue.push({child_generator.get(), current_level + 1});
        }
        if (current_level > max_level)
            max_level = current_level;
    }

    // construct the result
    std::vector<std::unordered_set<Generator *>> result;
    // notice that max is exclusive
    result.resize(max_level + 1);
    for (auto const &[generator_node, level]: level_index) {
        result[level].emplace(generator_node->generator);
    }
    return result;
}