#ifndef KRATOS_EXCEPT_HH
#define KRATOS_EXCEPT_HH

#include <vector>
#include "context.hh"

namespace kratos {

class VarException : public std::runtime_error {
public:
    VarException(const std::string &message, const std::vector<const Var *> &vars) noexcept;
};

class StmtException : public std::runtime_error {
public:
    StmtException(const std::string &message, const std::vector<Stmt *> &stmts) noexcept;
};

}  // namespace kratos

#endif  // KRATOS_EXCEPT_HH
