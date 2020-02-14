#ifndef KRATOS_FORMAL_HH
#define KRATOS_FORMAL_HH
#include "generator.hh"

namespace kratos {

// this is so that yosys won't freak out
void remove_async_reset(Generator* top);

}

#endif  // KRATOS_FORMAL_HH
