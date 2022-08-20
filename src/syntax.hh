#ifndef KRATOS_SV_SYNTAX_HH
#define KRATOS_SV_SYNTAX_HH

#include <string>
#include <optional>
#include <set>

namespace kratos {

// system verilog reserved keywords
bool is_valid_variable_name(const std::string &name);

struct BuiltinFunctionInfo {
    // 0 means void
    uint32_t return_width;
    bool synthesizable;
    uint32_t min_num_args = 1;
    uint32_t max_num_args = 1;
    bool signed_ = false;
};

std::optional<BuiltinFunctionInfo> get_builtin_function_info(const std::string &name);
std::set<std::string> get_builtin_function_names();

}  // namespace kratos

#endif  // KRATOS_SV_SYNTAX_HH
