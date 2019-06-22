#include "pass.hh"
#include "generator.hh"
#include "fmt/format.h"

using fmt::format;
using std::runtime_error;

void AssignmentTypeVisitor::visit(AssignStmt* stmt) {
    if (stmt->assign_type() == AssignmentType::Undefined) {
        stmt->set_assign_type(type_);
    } else if (check_type_ && stmt->assign_type() != type_) {
        throw ::runtime_error(::format("mismatch in assignment type"));
    }
}

void AssignmentTypeBlockVisitor::visit(SequentialStmtBlock* block) {
    AssignmentTypeVisitor visitor(AssignmentType::NonBlocking, true);
    visitor.visit_root(block->ast_node());
}

void AssignmentTypeBlockVisitor::visit(CombinationalStmtBlock* block) {
    AssignmentTypeVisitor visitor(AssignmentType::NonBlocking, true);
    visitor.visit_root(block->ast_node());
}

void fix_assignment_type(Generator* generator) {
    // first we fix all the block assignment
    AssignmentTypeBlockVisitor visitor;
    visitor.visit_root(generator->ast_node());

    // then we assign any existing assignment as blocking assignment
    AssignmentTypeVisitor final_visitor(AssignmentType::Blocking, false);
    final_visitor.visit_root(generator->ast_node());
}