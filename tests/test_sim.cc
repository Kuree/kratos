#include "../src/sim.hh"
#include "../src/stmt.hh"
#include "gtest/gtest.h"

using namespace kratos;

TEST(sim, value_scalar) {  // NOLINT
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

TEST(sim, value_array) {  // NOLINT
    Context context;
    auto &mod = context.generator("mod");
    auto &a = mod.var("a", 4, {2, 2});
    auto &b = mod.var("b", 4, {2, 2});
    auto &c = mod.var("c", 4);
    mod.add_stmt(c.assign(a[1][1]));
    mod.add_stmt(a.assign(b));

    Simulator sim(&mod);
    uint32_t constexpr value = 5;
    sim.set_complex_value(&(b[1][1]), std::vector<uint64_t>{value});

    sim.eval();

    auto res = sim.get_value(&c);
    EXPECT_TRUE(res != std::nullopt);
    EXPECT_EQ(*res, value);
}

TEST(sim, combinational_order_wrong) {  // NOLINT
    Context context;
    auto &mod = context.generator("mod");
    auto &a = mod.var("a", 4, {2, 2});
    auto &b = mod.var("b", 4, {2, 2});
    auto &c = mod.var("c", 4);
    auto comb = mod.combinational();
    comb->add_stmt(c.assign(a[1][1]));
    comb->add_stmt(a.assign(b));

    Simulator sim(&mod);
    uint32_t constexpr value = 5;
    sim.set_complex_value(&(b[1][1]), std::vector<uint64_t>{value});

    sim.eval();

    auto res = sim.get_value(&c);
    EXPECT_TRUE(res == std::nullopt);
}

TEST(sim, combinational_order_correct) {  // NOLINT
    Context context;
    auto &mod = context.generator("mod");
    auto &a = mod.var("a", 4, {2, 2});
    auto &b = mod.var("b", 4, {2, 2});
    auto &c = mod.var("c", 4);
    auto comb = mod.combinational();
    comb->add_stmt(a.assign(b));
    comb->add_stmt(c.assign(a[1][1]));

    Simulator sim(&mod);
    uint32_t constexpr value = 5;
    sim.set_complex_value(&(b[1][1]), std::vector<uint64_t>{value});

    sim.eval();

    auto res = sim.get_value(&c);
    EXPECT_TRUE(res != std::nullopt);
    EXPECT_EQ(*res, value);
}

TEST(sim, sequential) {  // NOLINT
    Context context;
    auto &mod = context.generator("mod");
    auto &clk = mod.var("clk", 1);
    auto &a = mod.var("a", 4, {2, 2});
    auto &b = mod.var("b", 4, {2, 2});
    auto &c = mod.var("c", 4);
    auto seq = mod.sequential();
    seq->add_condition({BlockEdgeType::Posedge, clk.shared_from_this()});
    seq->add_stmt(c.assign(a[1][1]));
    seq->add_stmt(a.assign(b));

    Simulator sim(&mod);
    uint32_t constexpr value = 5;
    sim.set_complex_value(&(b[1][1]), std::vector<uint64_t>{value});
    sim.eval();
    auto res = sim.get_value(&c);
    // should be null value
    EXPECT_TRUE(res == std::nullopt);

    sim.set_value(&clk, 1);
    sim.eval();
    res = sim.get_value(&c);
    EXPECT_TRUE(res == std::nullopt);

    sim.set_value(&clk, 0);
    sim.set_value(&clk, 1);
    sim.eval();
    res = sim.get_value(&c);
    EXPECT_TRUE(res != std::nullopt);
    EXPECT_EQ(*res, value);
}