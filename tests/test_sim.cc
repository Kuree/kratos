#include <random>
#include "../src/eval.hh"
#include "../src/sim.hh"
#include "../src/stmt.hh"
#include "../src/util.hh"
#include "gtest/gtest.h"

using namespace kratos;

TEST(sim, slicing_bit) {  // NOLINT
    Context context;
    auto &mod = context.generator("mod");
    auto &a = mod.var("a", 3);
    auto [high, low] = compute_var_high_low(&a, {{1, 1}});
    EXPECT_EQ(high, 1);
    EXPECT_EQ(low, 1);
    auto &b = mod.var("b", 4, {2, 2});
    std::tie(high, low) = compute_var_high_low(&b, {{1, 1}, {1, 1}});
    EXPECT_EQ(high, 4 * 4 - 1);
    EXPECT_EQ(low, 4 * 3);
}

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
    sim.set(&b, 1);

    auto res = sim.get(&c);
    EXPECT_TRUE(res != std::nullopt);
    EXPECT_EQ(*res, 2);
}

TEST(sim, value_extend) {   // NOLINT
    Context context;
    auto &mod = context.generator("mod");
    auto &a = mod.var("a", 2);
    auto &b = mod.var("b", 2);
    mod.add_stmt(b.assign(a[0].extend(2) + a[1].extend(2)));

    Simulator sim(&mod);
    sim.set(&a, 2);
    auto res = sim.get(&b);
    EXPECT_TRUE(res != std::nullopt);
    EXPECT_EQ(*res, 1);
}

TEST(sim, value_array) {  // NOLINT
    Context context;
    auto &mod = context.generator("mod");
    auto &a = mod.var("a", 4, {2, 2});
    auto &b = mod.var("b", 4, {2, 2});
    auto &d = mod.var("d", 2, std::vector<uint32_t>{2});
    d.set_is_packed(true);
    auto &c = mod.var("c", 4);
    mod.add_stmt(a.assign(b));
    mod.add_stmt(c.assign(a[1][1]));
    mod.add_stmt(d.assign(constant(4, 4)));

    Simulator sim(&mod);
    uint32_t constexpr value = 5;
    sim.set(&(b[1][1]), std::vector<uint64_t>{value});

    auto res = sim.get(&c);
    EXPECT_TRUE(res != std::nullopt);
    EXPECT_EQ(*res, value);

    res = sim.get(&d[1]);
    EXPECT_TRUE(res != std::nullopt);
    EXPECT_EQ(*res, 4 >> 2);
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
    sim.set(&(b[1][1]), std::vector<uint64_t>{value});

    auto res = sim.get(&c);
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
    sim.set(&(b[1][1]), std::vector<uint64_t>{value});

    auto res = sim.get(&c);
    EXPECT_TRUE(res != std::nullopt);
    EXPECT_EQ(*res, value);
}

TEST(sim, array_access) {   // NOLINT
    Context context;
    auto &mod = context.generator("mod");
    auto &a = mod.var("a", 4, 4);
    auto &b = mod.var("b", 2);

    Simulator sim(&mod);
    uint32_t constexpr value = 5;
    sim.set(&b, 2ul);
    sim.set(&a[b.shared_from_this()], value);

    auto res = sim.get(&a[b.shared_from_this()]);
    EXPECT_TRUE(res != std::nullopt);
    EXPECT_EQ(*res, value);
    res = sim.get(&a[2]);
    EXPECT_EQ(*res, 5);
}

TEST(sim, sequential) {  // NOLINT
    Context context;
    auto &mod = context.generator("mod");
    auto &clk = mod.var("clk", 1);
    auto &a = mod.var("a", 4, {2, 2});
    auto &b = mod.var("b", 4, {2, 2});
    auto &c = mod.var("c", 4);
    auto seq = mod.sequential();
    seq->add_condition({EventEdgeType::Posedge, clk.shared_from_this()});
    seq->add_stmt(c.assign(a[1][1]));
    seq->add_stmt(a.assign(b));

    Simulator sim(&mod);
    uint32_t constexpr value = 5;
    sim.set(&(b[1][1]), std::vector<uint64_t>{value});
    auto res = sim.get(&c);
    // should be null value
    EXPECT_TRUE(res == std::nullopt);

    sim.set(&clk, 1);
    sim.eval();
    res = sim.get(&c);
    EXPECT_TRUE(res == std::nullopt);

    sim.set(&clk, 0);
    sim.set(&clk, 1);
    res = sim.get(&c);
    EXPECT_TRUE(res != std::nullopt);
    EXPECT_EQ(*res, value);
}

TEST(sim, pull_up) {    // NOLINT
    Context context;
    auto &mod = context.generator("mod");
    auto &a = mod.var("a", 1);
    mod.add_stmt(a.assign(constant(1, 1)));

    Simulator sim(&mod);
    auto v = sim.get(&a);
    EXPECT_EQ(*v, 1);
}

TEST(sim, if_) {  // NOLINT
    Context context;
    auto &mod = context.generator("mod");
    auto &a = mod.var("a", 1);
    auto &b = mod.var("b", 1);
    auto &in = mod.port(PortDirection::In, "in", 1);
    auto comb = mod.combinational();
    auto if_ = std::make_shared<IfStmt>((in.eq(constant(1, 1))).shared_from_this());
    if_->add_then_stmt(a.assign(b));
    comb->add_stmt(if_);

    Simulator sim(&mod);
    auto v = sim.get(&a);
    EXPECT_EQ(v, std::nullopt);
    sim.set(&in, 1);
    sim.set(&b, 1);
    v = sim.get(&a);
    EXPECT_EQ(*v, 1);
}

TEST(sim, case_) {  // NOLINT
    Context context;
    auto &mod = context.generator("mod");
    auto &a = mod.var("a", 1);
    auto &b = mod.var("b", 1);
    auto &in = mod.port(PortDirection::In, "in", 1);
    auto comb = mod.combinational();
    auto case_ = std::make_shared<SwitchStmt>(in);
    case_->add_switch_case(constant(1, 1).as<Const>(), a.assign(b));
    case_->add_switch_case(nullptr, a.assign(constant(0, 1)));
    comb->add_stmt(case_);

    Simulator sim(&mod);
    auto v = sim.get(&a);
    EXPECT_EQ(v, std::nullopt);
    sim.set(&in, 1);
    sim.set(&b, 1);
    v = sim.get(&a);
    EXPECT_EQ(*v, 1);
}

TEST(sim, expr) {   // NOLINT
    Context context;
    auto &mod = context.generator("mod");
    auto &a = mod.port(PortDirection::In, "a", 16);
    auto &expr = a + a + a + a;
    auto &b = mod.port(PortDirection::Out, "b", 16);
    auto &c = mod.var("c", a.width() + b.width());
    mod.add_stmt(b.assign(expr));
    mod.add_stmt(c.assign(a.concat(b)));

    Simulator sim(&mod);
    auto v = sim.get(&b);
    EXPECT_EQ(v, std::nullopt);
    sim.set(&a, 2);
    v = sim.get(&b);
    EXPECT_EQ(*v, 2 * 4);
    v = sim.get(&c);
    EXPECT_EQ(*v, 2u << 16u | 2u * 4);
}

TEST(eval, bin_op) {  // NOLINT
    size_t seed = 42;
    std::mt19937 rnd;  // NOLINT
    rnd.seed(seed);
    auto constexpr width = 10;
    auto constexpr mask = UINT64_MASK >> (64u - width);
    auto constexpr num_test = 420u;
    std::vector<std::pair<int64_t, int64_t>> input_pairs(num_test);
    std::vector<std::pair<uint64_t, uint64_t>> eval_pairs(num_test);
    for (uint32_t i = 0; i < num_test; i++) {
        int64_t value1_ = static_cast<int64_t>(rnd() % mask) - mask / 2;
        uint64_t value1 = *(reinterpret_cast<uint64_t *>(&value1_)) & mask;
        int64_t value2_ = 0;
        uint64_t value2 = 0;
        while (value2_ == 0) {
            value2_ = static_cast<int64_t>(rnd() % mask) - mask / 2;
            value2 = *(reinterpret_cast<uint64_t *>(&value2_)) & mask;
        }
        input_pairs[i] = {value1_, value2_};
        eval_pairs[i] = {value1, value2};
    }

    std::map<ExprOp, std::function<int64_t(int64_t, int64_t)>> func_map = {
        {ExprOp::Add, [](int64_t value1, int64_t value2) { return value1 + value2; }},
        {ExprOp::Minus, [](int64_t value1, int64_t value2) { return value1 - value2; }},
        {ExprOp::Multiply, [](int64_t value1, int64_t value2) { return value1 * value2; }},
        {ExprOp::Divide, [](int64_t value1, int64_t value2) { return value1 / value2; }},
        {ExprOp::And, [](int64_t value1, int64_t value2) { return value1 & value2; }},  // NOLINT
        {ExprOp::Or, [](int64_t value1, int64_t value2) { return value1 | value2; }},   // NOLINT
        {ExprOp::Xor, [](int64_t value1, int64_t value2) { return value1 ^ value2; }},  // NOLINT
        {ExprOp::Eq, [](int64_t value1, int64_t value2) { return value1 == value2; }},
        {ExprOp::GreaterEqThan, [](int64_t value1, int64_t value2) { return value1 >= value2; }},
        {ExprOp::GreaterThan, [](int64_t value1, int64_t value2) { return value1 > value2; }},
        {ExprOp::LessEqThan, [](int64_t value1, int64_t value2) { return value1 <= value2; }},
        {ExprOp::LessThan, [](int64_t value1, int64_t value2) { return value1 < value2; }}};

    for (auto const &[op, func] : func_map) {
        // signed
        for (uint64_t i = 0; i < input_pairs.size(); i++) {
            auto const &[v1_, v2_] = input_pairs[i];
            auto const &[v1, v2] = eval_pairs[i];
            auto gold = func(v1_, v2_);
            auto result = eval_bin_op(v1, v2, op, width, true);
            if (gold < 0 || static_cast<uint64_t>(abs(gold)) > mask) {
                gold = (*reinterpret_cast<uint64_t *>(&gold)) & mask;
            }
            EXPECT_EQ(gold, result);
        }
        // unsigned
        for (auto [v1_, v2_] : input_pairs) {
            v1_ += mask / 2;
            v2_ += mask / 2;
            auto v1 = static_cast<uint64_t>(v1_);
            auto v2 = static_cast<uint64_t>(v2_);
            if (v2 == 0) continue;
            auto gold = truncate(func(v1_, v2_), width);
            auto result = eval_bin_op(v1, v2, op, width, false);
            EXPECT_EQ(gold, result);
        }
    }
}

TEST(eval, ternary) {    // NOLINT
    size_t seed = 42;
    std::mt19937 rnd;  // NOLINT
    rnd.seed(seed);
    auto constexpr width = 10;
    auto constexpr mask = UINT64_MASK >> (64u - width);
    auto constexpr num_test = 420u;
    for (uint32_t i = 0; i < num_test; i++) {
        uint64_t v1 = rnd() % mask;
        uint64_t v2 = rnd() % mask;
        bool p = rnd() % 2;
        auto result = eval_ternary_op(p, v1, v2, width);
        auto gold = p? v1: v2;
        EXPECT_EQ(result, gold);
    }
}

TEST(sim, ternary) {    // NOLINT
    Context ctx;
    auto &gen = ctx.generator("mod");
    auto &a = gen.var("a", 1);
    auto &b = gen.var("b", 16);
    auto &c = gen.var("c", 16);
    Simulator sim(&gen);
    sim.set(&a, 0);
    sim.set(&b, 42);
    sim.set(&c, 25);
    auto cond = ConditionalExpr(a.shared_from_this(), b.shared_from_this(), c.shared_from_this());
    auto result = (*sim.eval_expr(&cond))[0];
    EXPECT_EQ(result, 25);
    sim.set(&a, 1);
    result = (*sim.eval_expr(&cond))[0];
    EXPECT_EQ(result, 42);
}