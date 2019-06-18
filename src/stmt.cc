#include "stmt.hh"

AssignmentStmt::AssignmentStmt(const std::shared_ptr<Var>& left, const std::shared_ptr<Var>& right)
    : Stmt(StatementType ::Assign), left(left), right(right) {}