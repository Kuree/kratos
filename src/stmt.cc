#include "stmt.hh"

using std::move;

AssignStmt::AssignStmt(std::shared_ptr<Var> left, std::shared_ptr<Var> right)
    : AssignStmt(::move(left), ::move(right), AssignmentType::Undefined) {}

AssignStmt::AssignStmt(std::shared_ptr<Var> left, std::shared_ptr<Var> right, AssignmentType type)
    : Stmt(StatementType ::Assign),
      left_(::move(left)),
      right_(::move(right)),
      assign_type_(type) {}