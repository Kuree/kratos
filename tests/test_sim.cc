#include "../src/sim.hh"
#include "../src/stmt.hh"
#include "gtest/gtest.h"

using namespace kratos;

TEST(sim, value1) {  // NOLINT
    Context context;
    auto &mod = context.generator("mod");
    auto &a = mod.var("a", 1);
    auto &b = mod.var("b", 1);
    auto &c = mod.var("c", 3);
    mod.add_stmt(c[0].assign(constant(0, 1)));
    mod.add_stmt(c[1].assign(b));
    mod.add_stmt(a.assign(b));

    Simulator sim(&mod);
    sim.set_value(&b, 1);

    sim.eval();

    auto res = sim.get_value(&c);
    EXPECT_TRUE(res != std::nullopt);
    EXPECT_EQ(*res, 2);
}