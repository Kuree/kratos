#ifndef DUSK_PASS_HH
#define DUSK_PASS_HH

#include "ast.hh"
#include "context.hh"
#include "stmt.hh"
#include "hash.hh"

enum HashStrategy: int { SequentialHash, ParallelHash };

void fix_assignment_type(Generator* top);

void remove_unused_vars(Generator* top);

void verify_generator_connectivity(Generator* top);

void create_module_instantiation(Generator* top);

void hash_generators(Generator* top, HashStrategy strategy);

void uniquify_generators(Generator* top);

void uniquify_module_instances(Generator* top);

std::map<std::string, std::string> generate_verilog(Generator *top);

// TODO: add following passes to improve the code efficiency
//  1. check module hierarchy
//  2. remove an assignment
//  3. remove a var
//  4. remove a child generator

#endif  // DUSK_PASS_HH
