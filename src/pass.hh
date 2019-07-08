#ifndef KRATOS_PASS_HH
#define KRATOS_PASS_HH

#include <functional>
#include "ast.hh"
#include "context.hh"
#include "hash.hh"
#include "stmt.hh"

enum HashStrategy : int { SequentialHash, ParallelHash };

void fix_assignment_type(Generator* top);

void verify_assignments(Generator* top);

void remove_unused_vars(Generator* top);

void zero_out_stubs(Generator* top);

void verify_generator_connectivity(Generator* top);

void check_mixed_assignment(Generator* top);

void create_module_instantiation(Generator* top);

void hash_generators(Generator* top, HashStrategy strategy);

void decouple_generator_ports(Generator* top);

void uniquify_generators(Generator* top);

void uniquify_module_instances(Generator* top);

std::map<std::string, std::string> generate_verilog(Generator* top);

std::map<std::string, std::map<uint32_t, std::vector<std::pair<std::string, uint32_t>>>>
extract_debug_info(Generator* top);

std::map<std::string, std::string> extract_struct_info(Generator* top);

// TODO: add following passes to improve the code efficiency
//  1. check module hierarchy
//  2. remove an assignment
//  3. remove a var
//  4. remove a child generator

// These code below are optional passes that make the code more readable
void transform_if_to_case(Generator* top);

void remove_fanout_one_wires(Generator* top);

void remove_pass_through_modules(Generator* top);

class PassManager {
public:
    PassManager() = default;

    void add_pass(const std::string& name, std::function<void(Generator*)> fn);
    void add_pass(const std::string &name, void(fn)(Generator*));

    bool inline has_pass(const std::string& name) const {
        return passes_.find(name) != passes_.end();
    }

    void run_passes(Generator* generator);

    uint64_t num_passes()  const { return passes_order_.size(); }

private:
    std::map<std::string, std::function<void(Generator*)>> passes_;
    std::vector<std::string> passes_order_;
};

#endif  // KRATOS_PASS_HH
