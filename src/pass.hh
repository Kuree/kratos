#ifndef DUSK_PASS_HH
#define DUSK_PASS_HH

#include "ast.hh"
#include "context.hh"
#include "stmt.hh"
#include "hash.hh"

void fix_assignment_type(Generator* generator);

void remove_unused_vars(Generator* generator);

void verify_generator_connectivity(Generator* generator);

void create_module_instantiation(Generator* generator);

void hash_generators(Generator* generator, HashStrategy strategy);

std::map<std::string, std::string> generate_verilog(Generator *generator);

// TODO: add following passes to improve the code efficiency
//  1. check module hierarchy
//  2. remove an assignment
//  3. remove a var
//  4. remove a child generator

#endif  // DUSK_PASS_HH
