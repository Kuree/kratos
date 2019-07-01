#ifndef KRATOS_PASS_HH
#define KRATOS_PASS_HH

#include "ast.hh"
#include "context.hh"
#include "stmt.hh"
#include "hash.hh"

enum HashStrategy: int { SequentialHash, ParallelHash };

void fix_assignment_type(Generator* top);

void verify_assignments(Generator* top);

void remove_unused_vars(Generator* top);

void zero_out_stubs(Generator* top);

void verify_generator_connectivity(Generator* top);

void check_mixed_assignment(Generator* top);

void create_module_instantiation(Generator* top);

void hash_generators(Generator* top, HashStrategy strategy);

void decouple_generator_ports(Generator *top);

void uniquify_generators(Generator* top);

void uniquify_module_instances(Generator* top);

std::map<std::string, std::string> generate_verilog(Generator *top);


// TODO: add following passes to improve the code efficiency
//  1. check module hierarchy
//  2. remove an assignment
//  3. remove a var
//  4. remove a child generator

// These code below are optional passes that make the code more readable
void transform_if_to_case(Generator *top);

void remove_fanout_one_wires(Generator *top);

void remove_pass_through_modules(Generator *top);

#endif  // KRATOS_PASS_HH
