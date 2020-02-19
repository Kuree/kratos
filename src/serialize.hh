#ifndef KRATOS_SERIALIZE_HH
#define KRATOS_SERIALIZE_HH

#include <memory>
#include <ostream>

#include "context.hh"

namespace kratos {

void serialize(std::ostream &ostream, std::shared_ptr<Context> context);

}

#endif  // KRATOS_SERIALIZE_HH
