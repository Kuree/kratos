#ifndef KRATOS_PASS_HH
#define KRATOS_PASS_HH

#include <functional>
#include "context.hh"
#include "hash.hh"
#include "ir.hh"
#include "stmt.hh"

namespace kratos {

enum class HashStrategy : int { SequentialHash, ParallelHash };

void fix_assignment_type(Generator* top);

void verify_assignments(Generator* top);

void remove_unused_vars(Generator* top);

void remove_unused_stmts(Generator* top);

void zero_out_stubs(Generator* top);

void verify_generator_connectivity(Generator* top);

void zero_generator_inputs(Generator* top);

void check_mixed_assignment(Generator* top);

void check_non_synthesizable_content(Generator* top);

void check_active_high(Generator* top);

void create_module_instantiation(Generator* top);

void create_interface_instantiation(Generator *top);

void hash_generators(Generator* top, HashStrategy strategy);
void inline hash_generators_parallel(Generator* top) {
    hash_generators(top, HashStrategy::ParallelHash);
}
void inline hash_generators_sequential(Generator* top) {
    hash_generators(top, HashStrategy::SequentialHash);
}

void decouple_generator_ports(Generator* top);

void uniquify_generators(Generator* top);

void check_function_return(Generator* top);

void check_inferred_latch(Generator *top);

void check_multiple_driver(Generator *top);

void check_combinational_loop(Generator *top);

void check_flip_flop_always_ff(Generator *top);

void remove_empty_block(Generator *top);

void change_property_into_stmt(Generator *top);

std::map<std::string, std::string> generate_verilog(Generator* top);
// this function outputs every module into a single file in the targeted direction
// if header filename is not empty,
void generate_verilog(Generator* top, const std::string& output_dir, const std::string& package_name,
                      bool debug);

std::map<std::string, std::map<uint32_t, std::vector<std::pair<std::string, uint32_t>>>>
extract_debug_info(Generator* top);

std::map<std::string, std::string> extract_struct_info(Generator* top);

std::map<std::string, std::string> extract_dpi_function(Generator* top, bool int_interface);

std::map<std::string, std::string> extract_enum_info(Generator *top);

std::map<std::string, std::string> extract_interface_info(Generator *top);

std::vector<std::string> extract_register_names(Generator *top);
std::vector<std::string> extract_var_names(Generator *top);

void check_always_sensitivity(Generator *top);

// TODO: add following passes to improve the code efficiency
//  1. check module hierarchy
//  2. remove an assignment
//  3. remove a var
//  4. remove a child generator

// These code below are optional passes that make the code more readable
void transform_if_to_case(Generator* top);

void merge_if_block(Generator* top);

void remove_fanout_one_wires(Generator* top);

void remove_pass_through_modules(Generator* top);

void merge_wire_assignments(Generator* top);

void insert_pipeline_stages(Generator* top);

void auto_insert_clock_enable(Generator *top);

void auto_insert_sync_reset(Generator *top);

void change_port_bundle_struct(Generator* top);

void realize_fsm(Generator* top);

void sort_stmts(Generator* top);

void ssa_transform_fix(Generator *top);

class PassManager {
public:
    PassManager() = default;

    void register_pass(const std::string& name, std::function<void(Generator*)> fn);
    void register_pass(const std::string& name, void(fn)(Generator*));
    void add_pass(const std::string& name);

    [[nodiscard]] bool inline has_pass(const std::string& name) const {
        return passes_.find(name) != passes_.end();
    }

    void register_builtin_passes();

    void run_passes(Generator* generator);

    [[nodiscard]] uint64_t num_passes() const { return passes_order_.size(); }

private:
    std::map<std::string, std::function<void(Generator*)>> passes_;
    std::vector<std::string> passes_order_;
};

}  // namespace kratos

#endif  // KRATOS_PASS_HH
