#include "NanoLog.hpp"
#include "codegen.h"
#include "context.hh"
#include "expr.hh"
#include "pass.hh"


VerilogModule::VerilogModule(Generator *generator) {
    // run multiple passes
    // LOG_INFO << "Running pass: fix_assignment_type";
    fix_assignment_type(generator);

    zero_out_stubs(generator);

    // LOG_INFO << "Running pass:  remove_unused_vars";
    remove_unused_vars(generator);
    verify_assignments(generator);
    // LOG_INFO << "Running pass: verify_generator_connectivity";
    verify_generator_connectivity(generator);
    // TODO:
    //  add decouple-wire
    //  add inline pass
    // LOG_INFO << "Running pass: create_module_instantiation";
    create_module_instantiation(generator);
    // LOG_INFO << "Running pass: uniquify_generators";
    uniquify_generators(generator);
    // LOG_INFO << "Running pass: uniquify_module_instances";
    uniquify_module_instances(generator);
    // LOG_INFO << "Running pass: create_module_instantiation";
    create_module_instantiation(generator);
    // LOG_INFO << "Running pass: generate_verilog";
    verilog_src_ = generate_verilog(generator);

}