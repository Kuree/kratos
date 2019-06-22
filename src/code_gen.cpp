#include "NanoLog.hpp"
#include "code_gen.h"
#include "context.hh"
#include "expr.hh"
#include "pass.hh"


VerilogModule::VerilogModule(Generator *generator) {
    // run multiple passes
    LOG_INFO << "Running pass: fix_assignment_type";
    fix_assignment_type(generator);
    LOG_INFO << "Remove unused variables";
    remove_unused_vars(generator);
}