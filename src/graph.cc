#include "graph.hh"
#include <unordered_set>
#include "ast.hh"
#include "fmt/format.h"
#include "generator.hh"

using fmt::format;

class GeneratorVisitor : public ASTVisitor {
public:
    explicit GeneratorVisitor(GeneratorGraph *g) : g_(g) {}
    void visit_generator(Generator *generator) override { g_->add_node(generator); }

private:
    GeneratorGraph *g_;
};

class GeneratorGraphVisitor : public ASTVisitor {
public:
    explicit GeneratorGraphVisitor(GeneratorGraph *g) : g_(g) {}
    void visit_generator(Generator *generator) override {
        auto parent_node = g_->get_node(generator);
        for (auto const &child : generator->get_child_generators()) {
            auto child_node = g_->get_node(child.get());
            if (child_node->parent != nullptr)
                throw std::runtime_error(::format("{0} already has a parent",
                                                  child_node->parent->generator->instance_name));
            child_node->parent = parent_node;
            parent_node->children.emplace(child_node);
        }
    }

private:
    GeneratorGraph *g_;
};

GeneratorGraph::GeneratorGraph(Generator *generator): root_(generator) {
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

std::queue<GeneratorNode*> GeneratorGraph::topological_sort() {
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

std::vector<Generator*> GeneratorGraph::get_sorted_generators() {
    auto queue = topological_sort();
    std::vector<Generator*> result;
    result.reserve(queue.size());
    while (!queue.empty()) {
        result.emplace_back(queue.front());
        queue.pop();
    }
    return result;
}