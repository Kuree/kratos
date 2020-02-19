#include "../src/serialize.hh"
#include "gtest/gtest.h"
#include <sstream>

namespace kratos {

std::shared_ptr<Context> context() { return std::make_shared<Context>(); }

TEST(serialize, generator) {    // NOLINT
    auto c_ptr = context();
    auto &c = *c_ptr;
    c.generator("mod");

    std::ostringstream s;
    serialize(s, &c);
    printf("%s\n", s.str().c_str());
}

}