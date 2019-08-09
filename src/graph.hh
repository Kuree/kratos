#ifndef KRATOS_GRAPH_HH
#define KRATOS_GRAPH_HH

#include <queue>
#include <unordered_set>
#include <vector>
#include "context.hh"

namespace kratos {

struct GeneratorNode {
    GeneratorNode *parent = nullptr;
    Generator *generator;
    std::set<Generator *> children;
};

class GeneratorGraph {
public:
    explicit GeneratorGraph(Generator *);
    GeneratorNode *add_node(Generator *generator);
    GeneratorNode *get_node(Generator *generator);
    std::vector<Generator *> get_sorted_generators();
    std::vector<std::vector<Generator *>> get_leveled_generators();

private:
    std::unordered_map<Generator *, GeneratorNode> nodes_;
    std::queue<GeneratorNode *> topological_sort();

    Generator *root_;
};

struct StmtNode {
    StmtNode *parent = nullptr;
    Stmt *stmt;
    std::set<StmtNode*> children;
};

class StatementGraph {
public:
    explicit StatementGraph(StmtBlock *stmt);

private:
    std::unordered_map<Stmt*, StmtNode> nodes_;
    StmtNode *root_;

    void build_graph();
    void add_stmt_child(Stmt* stmt);
};

}  // namespace kratos
#endif  // KRATOS_GRAPH_HH
