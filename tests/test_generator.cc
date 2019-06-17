#include "../src/expr.hh"
#include "../src/generator.hh"
#include "gtest/gtest.h"

TEST(generator, load) {  // NOLINT
    Context c;
    auto mod = Generator::from_verilog(&c, "module1.sv", "module1", {}, {});
    EXPECT_TRUE(mod.get_port("f") != nullptr);
    mod = Generator::from_verilog(&c, "module1.sv", "module2", {}, {});
    EXPECT_TRUE(mod.get_port("f") != nullptr);
    mod = Generator::from_verilog(&c, "module1.sv", "module3", {}, {});
    EXPECT_TRUE(mod.get_port("f") != nullptr);
    ASSERT_ANY_THROW(Generator::from_verilog(&c, "module1.sv", "module1", {"NON_EXIST"}, {}));
    mod = Generator::from_verilog(&c, "module1.sv", "module1", {}, {{"a", PortType::Clock}});
    EXPECT_EQ(mod.get_port("a")->type, PortType::Clock);
    ASSERT_ANY_THROW(
        Generator::from_verilog(&c, "module1.sv", "module1", {}, {{"aa", PortType::Clock}}));
}

TEST(generator, port) {  // NOLINT
    Context c;
    auto mod = c.generator("module");
    mod.port(PortDirection::In, "in", 1);
    mod.port(PortDirection::Out, "out", 1);
}

TEST(generator, expr) {  // NOLINT
    Context c;
    auto mod = c.generator("module");
    Port &p_in = mod.port(PortDirection::In, "in", 1);
    Port &p_out = mod.port(PortDirection::Out, "out", 1);

    Var &var1 = mod.var("a", 1);
    Var var2 = mod.var("b", 1);
    auto expr = var1 + var2;
    EXPECT_EQ(expr.left.get(), &var1);
    // var2 is stored in stack
    EXPECT_NE(expr.right.get(), &var2);

    expr = p_in + p_out;
    EXPECT_EQ(expr.name, "(in + out)");

    expr = (var1 - var2).ashr(var2);
    EXPECT_EQ(expr.name, "((a - b) >>> b)");

    // test auto collapsing
    auto &expr1 = var1 - var2;
    auto &expr2 = var1 - var2;
    // they should point to the same memory address
    EXPECT_EQ(&expr1, &expr2);

    // test unary
    auto expr_unary = -var1;
    EXPECT_EQ(expr_unary.name, "(- a)");
}