#include "stmt.hh"

using std::move;

AssignStmt::AssignStmt(std::shared_ptr<Var> left, std::shared_ptr<Var> right)
    : AssignStmt(::move(left), ::move(right), AssignmentType::Undefined) {}

AssignStmt::AssignStmt(std::shared_ptr<Var> left, std::shared_ptr<Var> right, AssignmentType type)
    : Stmt(StatementType ::Assign),
      left_(::move(left)),
      right_(::move(right)),
      assign_type_(type) {}

IfStmt::IfStmt(std::shared_ptr<Var> predicate)
    : Stmt(StatementType::If), predicate_(::move(predicate)) {}

void IfStmt::add_then_stmt(std::shared_ptr<Stmt> stmt) {
    then_body_.emplace_back(::move(stmt));
}

void IfStmt::add_else_stmt(std::shared_ptr<Stmt> stmt) {
    else_body_.emplace_back(::move(stmt));
}