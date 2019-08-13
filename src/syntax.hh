#ifndef KRATOS_SV_SYNTAX_HH
#define KRATOS_SV_SYNTAX_HH

#include <unordered_set>

namespace kratos {

// system verilog reserved keywords
bool is_valid_variable_name(const std::string &name);

}  // namespace kratos

#endif  // KRATOS_SV_SYNTAX_HH
