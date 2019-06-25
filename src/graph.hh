#ifndef DUSK_GRAPH_HH
#define DUSK_GRAPH_HH

#include <queue>
#include <vector>
#include <unordered_set>
#include "context.hh"


struct GeneratorNode {
    GeneratorNode *parent = nullptr;
    Generator* generator;
    std::set<Generator*> children;
};

class GeneratorGraph {
public:
    explicit GeneratorGraph(Generator*);
    GeneratorNode* add_node(Generator *generator);
    GeneratorNode* get_node(Generator *generator);
    std::vector<Generator*> get_sorted_generators();
    std::vector<std::unordered_set<Generator*>> get_leveled_generators();

private:
    std::unordered_map<Generator*, GeneratorNode> nodes_;
    std::queue<GeneratorNode*> topological_sort();

    Generator *root_;
};


#endif //DUSK_GRAPH_HH
