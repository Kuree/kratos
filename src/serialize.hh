#ifndef KRATOS_SERIALIZE_HH
#define KRATOS_SERIALIZE_HH

#include <memory>
#include <ostream>
#include <istream>

#include "context.hh"

namespace kratos {

void serialize(std::ostream &ostream, std::shared_ptr<Context> context);

void serialize(std::ostream &ostream, std::shared_ptr<Generator> generator);

std::shared_ptr<Generator> load_generator(std::istream &stream);

}

#endif  // KRATOS_SERIALIZE_HH
