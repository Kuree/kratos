#include "pass.hh"
#include <algorithm>
#include "fmt/format.h"
#include "generator.hh"

using fmt::format;
using std::runtime_error;

class AssignmentTypeVisitor : public ASTVisitor {
public:
    explicit AssignmentTypeVisitor(AssignmentType type, bool check_type = true)
        : ASTVisitor(), type_(type), check_type_(check_type) {}
    void visit(AssignStmt* stmt) override {
        if (stmt->assign_type() == AssignmentType::Undefined) {
            stmt->set_assign_type(type_);
        } else if (check_type_ && stmt->assign_type() != type_) {
            throw ::runtime_error(::format("mismatch in assignment type"));
        }
    }

private:
    AssignmentType type_;
    bool check_type_;
};

class AssignmentTypeBlockVisitor : public ASTVisitor {
    void visit(CombinationalStmtBlock* block) override {
        AssignmentTypeVisitor visitor(AssignmentType::NonBlocking, true);
        visitor.visit_root(block->ast_node());
    }
    void visit(SequentialStmtBlock* block) override {
        AssignmentTypeVisitor visitor(AssignmentType::NonBlocking, true);
        visitor.visit_root(block->ast_node());
    }
};

void fix_assignment_type(Generator* generator) {
    // first we fix all the block assignment
    AssignmentTypeBlockVisitor visitor;
    visitor.visit_root(generator->ast_node());

    // then we assign any existing assignment as blocking assignment
    AssignmentTypeVisitor final_visitor(AssignmentType::Blocking, false);
    final_visitor.visit_root(generator->ast_node());
}

class VarAccumulationVisitor : public ASTVisitor {
public:
    VarAccumulationVisitor() : ASTVisitor(), vars() {}
    void visit(Var* var) override {
        if (var->type() == VarType ::Base) vars.emplace(var->name);
    }
    std::set<std::string> vars;
};

void remove_unused_vars(Generator* generator) {
    // get a set of all variables
    std::set<std::string> var_names;
    for (auto const& [var_name, var] : generator->vars()) {
        if (var->type() == VarType::Base) var_names.emplace(var_name);
    }
    // visit each assignment to see if we have used it or not
    VarAccumulationVisitor visitor;
    visitor.visit_root(generator);

    // result set
    std::set<std::string> diff_set;
    std::set_difference(var_names.begin(), var_names.end(), visitor.vars.begin(),
                        visitor.vars.end(), std::inserter(diff_set, diff_set.end()));
    for (const auto& var_name : diff_set) {
        generator->remove_var(var_name);
    }
}