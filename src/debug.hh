#ifndef KRATOS_DEBUG_HH
#define KRATOS_DEBUG_HH

#include "stmt.hh"

namespace kratos {

std::unordered_map<Stmt*, uint32_t> inject_debug_break_points(Generator *top);

void insert_debugger_setup(Generator *top);

}  // namespace kratos
#endif  // KRATOS_DEBUG_HH
