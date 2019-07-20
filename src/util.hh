#ifndef KRATOS_UTIL_HH
#define KRATOS_UTIL_HH

#include "expr.hh"
#include "stmt.hh"

namespace kratos {


std::string ExprOpStr(ExprOp op);

// may need to look at this https://stackoverflow.com/q/28828957
std::string var_type_to_string(VarType type);

std::string ast_type_to_string(IRNodeKind kind);

std::string assign_type_to_str(AssignmentType type);

std::string port_dir_to_str(PortDirection direction);

std::string port_type_to_str(PortType type);

bool is_valid_verilog(const std::string &src);

}

#endif  // KRATOS_UTIL_HH
