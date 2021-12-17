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
    std::vector<Generator *> get_sorted_nodes();
    std::vector<std::vector<Generator *>> get_leveled_nodes();

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
    explicit StatementGraph(Generator *generator);
    [[nodiscard]] const std::unordered_map<Stmt*, StmtNode> &nodes() const { return nodes_; }

private:
    std::unordered_map<Stmt*, StmtNode> nodes_;
    Generator *root_;

    void build_graph();
    void add_stmt_child(Stmt* stmt);
};

class PackedStruct;
struct PackedStructNode {
    PackedStructNode *parent = nullptr;
    const PackedStruct *struct_;
    std::set<PackedStructNode*> children;
};

class PackedStructGraph {
public:
    PackedStructNode * add_node(const PackedStruct *s);
    PackedStructNode *get_node(const PackedStruct *value);
    std::vector<const PackedStruct*> get_structs();
    [[nodiscard]] bool has_node(const PackedStruct *s) const;

private:
    std::unordered_map<std::string, PackedStructNode> nodes_;
};

}  // namespace kratos
#endif  // KRATOS_GRAPH_HH
