#ifndef KRATOS_AST_HH
#define KRATOS_AST_HH

#include <cstdint>
#include <vector>
#include "context.hh"

class ASTVisitor;

enum ASTNodeKind { GeneratorKind, VarKind, StmtKind };


class Attribute {
public:
    virtual ~Attribute() = default;
    std::string type_str;
    std::string value_str;

    void *get() { return target_; }
    void set(void *target) { target_ = target; }

private:
    void* target_ = nullptr;
};

struct ASTNode {
public:
    explicit ASTNode(ASTNodeKind type) : ast_node_type_(type) {}

    virtual void accept(ASTVisitor *) {}
    virtual uint64_t child_count() { return 0; }
    virtual ASTNode *get_child(uint64_t) { return nullptr; }

    ASTNode *ast_node() { return this; }

    virtual ASTNode *parent() { return nullptr; }
    ASTNodeKind ast_node_kind() { return ast_node_type_; }

    std::vector<std::pair<std::string, uint32_t>> fn_name_ln;

    uint32_t verilog_ln = 0;

    // attributes for passes
    const std::vector<std::shared_ptr<Attribute>> &get_attributes() const { return attributes_; }
    void add_attribute(const std::shared_ptr<Attribute> &attribute) {
        attributes_.emplace_back(attribute);
    }

private:
    ASTNodeKind ast_node_type_;
    std::vector<std::shared_ptr<Attribute>> attributes_;
};

class ASTVisitor {
public:
    virtual void visit_root(ASTNode *root);
    // visit generators only
    virtual void visit_generator_root(Generator *generator);
    // visit current scope only
    virtual void visit_content(Generator *generator);

    // visit methods
    virtual inline void visit(Var *) {}
    virtual inline void visit(Port *) {}
    virtual inline void visit(VarSlice *) {}
    virtual inline void visit(VarConcat *) {}
    virtual inline void visit(Expr *) {}
    virtual inline void visit(Const *) {}
    virtual inline void visit(Parameter *) {}
    virtual inline void visit(AssignStmt *) {}
    virtual inline void visit(IfStmt *) {}
    virtual inline void visit(SwitchStmt *) {}
    virtual inline void visit(CombinationalStmtBlock *) {}
    virtual inline void visit(SequentialStmtBlock *) {}
    virtual inline void visit(ModuleInstantiationStmt *) {}

    // generator specific traversal
    virtual void visit(Generator *) {}

protected:
    uint32_t level = 0;

    std::unordered_set<ASTNode *> visited_;
};

// TODO
//  implement a proper AST transformer

#endif  // KRATOS_AST_HH
