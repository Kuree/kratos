#ifndef KRATOS_IR_HH
#define KRATOS_IR_HH

#include <cstdint>
#include <vector>
#include "context.hh"

namespace kratos {

class IRVisitor;

enum IRNodeKind { GeneratorKind, VarKind, StmtKind };

class Attribute {
public:
    virtual ~Attribute() = default;
    std::string type_str;
    std::string value_str;

    void *get() { return target_.get(); }
    void set(const std::shared_ptr<void> &target) { target_ = target; }

private:
    std::shared_ptr<void> target_ = nullptr;
};

struct IRNode {
public:
    explicit IRNode(IRNodeKind type) : ast_node_type_(type) {}

    virtual void accept(IRVisitor *) {}
    virtual uint64_t child_count() { return 0; }
    virtual IRNode *get_child(uint64_t) { return nullptr; }
    // the caller is responsible to check the return value; if it's larger than count + 1
    // it means its not found. default implementation is linear search
    virtual uint64_t index_of(IRNode* node);

    IRNode *ast_node() { return this; }

    virtual IRNode *parent() { return nullptr; }
    IRNodeKind ir_node_kind() { return ast_node_type_; }

    std::vector<std::pair<std::string, uint32_t>> fn_name_ln;

    uint32_t verilog_ln = 0;

    std::string comment;

    // attributes for passes
    [[nodiscard]] const std::vector<std::shared_ptr<Attribute>> &get_attributes() const {
        return attributes_;
    }
    void add_attribute(const std::shared_ptr<Attribute> &attribute) {
        attributes_.emplace_back(attribute);
    }

    virtual ~IRNode() = default;

private:
    IRNodeKind ast_node_type_;
    std::vector<std::shared_ptr<Attribute>> attributes_;
};

class IRVisitor {
public:
    virtual void visit_root(IRNode *root);
    // visit generators only
    virtual void visit_generator_root(Generator *generator);
    // the parallel version
    virtual void visit_generator_root_p(Generator *generator);

    // visit current scope only
    virtual void visit_content(Generator *generator);

    // visit methods
    virtual inline void visit(Var *) {}
    virtual inline void visit(Port *) {}
    virtual inline void visit(VarSlice *) {}
    virtual inline void visit(VarConcat *) {}
    virtual inline void visit(Expr *) {}
    virtual inline void visit(EnumVar *) {}
    virtual inline void visit(EnumConst *) {}
    virtual inline void visit(Const *) {}
    virtual inline void visit(Parameter *) {}
    virtual inline void visit(FunctionCallVar *) {}
    virtual inline void visit(AssignStmt *) {}
    virtual inline void visit(ScopedStmtBlock *) {}
    virtual inline void visit(IfStmt *) {}
    virtual inline void visit(SwitchStmt *) {}
    virtual inline void visit(CombinationalStmtBlock *) {}
    virtual inline void visit(SequentialStmtBlock *) {}
    virtual inline void visit(FunctionStmtBlock *) {}
    virtual inline void visit(InitialStmtBlock *) {}
    virtual inline void visit(FunctionCallStmt *) {}
    virtual inline void visit(ReturnStmt *) {}
    virtual inline void visit(ModuleInstantiationStmt *) {}

    // generator specific traversal
    virtual void visit(Generator *) {}

    virtual ~IRVisitor() = default;

protected:
    uint32_t level = 0;

    std::unordered_set<IRNode *> visited_;
};

// TODO
//  implement a proper IR transformer

}  // namespace kratos
#endif  // KRATOS_IR_HH
