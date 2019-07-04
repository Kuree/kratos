#ifndef KRATOS_EXCEPT_HH
#define KRATOS_EXCEPT_HH

#include "context.hh"
#include <vector>

class VarException: public std::runtime_error {
public:
    VarException(const std::string &message, const std::vector<Var*> &vars) noexcept;
};

class StmtException: public std::runtime_error {
public:
    StmtException(const std::string &message, const std::vector<Stmt*> &stmts) noexcept;
};


#endif //KRATOS_EXCEPT_HH
