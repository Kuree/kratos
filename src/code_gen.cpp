#include "NanoLog.hpp"
#include "code_gen.h"
#include "context.hh"
#include "expr.hh"
#include "pass.hh"


VerilogModule::VerilogModule(Generator *generator) {
    // run multiple passes
    LOG_INFO << "Running pass: fix_assignment_type";
    fix_assignment_type(generator);
    LOG_INFO << "Running pass:  remove_unused_vars";
    remove_unused_vars(generator);
    LOG_INFO << "Running pass: verify_generator_connectivity";
    verify_generator_connectivity(generator);
    // TODO:
    //  add unification
    //  add decouple-wire
    LOG_INFO << "Running pass: create_module_instantiation";
    create_module_instantiation(generator);
}