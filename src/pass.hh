#ifndef DUSK_PASS_HH
#define DUSK_PASS_HH

#include "ast.hh"
#include "context.hh"
#include "stmt.hh"

void fix_assignment_type(Generator* generator);

void remove_unused_vars(Generator* generator);

#endif  // DUSK_PASS_HH
