#ifndef KRATOS_UTIL_HH
#define KRATOS_UTIL_HH

#include "expr.hh"
#include "stmt.hh"

std::string ExprOpStr(ExprOp op);

// may need to look at this https://stackoverflow.com/q/28828957
std::string var_type_to_string(VarType type);

std::string ast_type_to_string(ASTNodeKind kind);

std::string assign_type_to_str(AssignmentType type);

std::string port_dir_to_str(PortDirection direction);

bool is_valid_verilog(const std::string &src);

#endif  // KRATOS_UTIL_HH
