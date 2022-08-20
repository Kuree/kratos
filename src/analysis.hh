#ifndef KRATOS_ANALYSIS_HH
#define KRATOS_ANALYSIS_HH
#include "generator.hh"

namespace kratos {

void verify_assignments(Generator *top);

void check_mixed_assignment(Generator *top);

void check_non_synthesizable_content(Generator *top);

void check_active_high(Generator *top);

void check_function_return(Generator *top);

void check_inferred_latch(Generator *top);

void check_multiple_driver(Generator *top);

void check_combinational_loop(Generator *top);

void check_flip_flop_always_ff(Generator *top);

std::unordered_map<const Stmt *, std::string> compute_enable_condition(Generator *top);

std::map<std::string, std::string> extract_struct_info(Generator *top);

std::map<std::string, std::string> extract_dpi_function(Generator *top, bool int_interface);

std::map<std::string, std::string> extract_enum_info(Generator *top);

std::map<std::string, std::string> extract_interface_info(Generator *top);

std::vector<std::string> extract_register_names(Generator *top);
std::vector<std::string> extract_var_names(Generator *top);

void check_always_sensitivity(Generator *top);

void verify_generator_connectivity(Generator* top);

}  // namespace kratos

#endif  // KRATOS_ANALYSIS_HH
