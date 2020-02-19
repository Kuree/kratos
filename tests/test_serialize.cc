#include "../src/serialize.hh"
#include "gtest/gtest.h"
#include <sstream>
#include "../src/generator.hh"

namespace kratos {

std::shared_ptr<Context> context() { return std::make_shared<Context>(); }

TEST(serialize, generator) {    // NOLINT
    auto c_ptr = context();
    auto &c = *c_ptr;
    auto &mod = c.generator("mod");
    mod.var("v", 1);

    std::ostringstream s;
    serialize(s, c_ptr);
    auto value = s.str();
    EXPECT_TRUE(!value.empty());
}

}