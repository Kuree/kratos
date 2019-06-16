#include "../src/expr.hh"
#include "../src/module.hh"
#include "gtest/gtest.h"

TEST(module, load) {  // NOLINT
    Context c;
    auto mod = Module::from_verilog(&c, "module1.sv", "module1", {}, {});
    EXPECT_TRUE(mod.get_port("f") != nullptr);
    mod = Module::from_verilog(&c, "module1.sv", "module2", {}, {});
    EXPECT_TRUE(mod.get_port("f") != nullptr);
    mod = Module::from_verilog(&c, "module1.sv", "module3", {}, {});
    EXPECT_TRUE(mod.get_port("f") != nullptr);
    ASSERT_ANY_THROW(Module::from_verilog(&c, "module1.sv", "module1", {"NON_EXIST"}, {}));
    mod = Module::from_verilog(&c, "module1.sv", "module1", {}, {{"a", PortType::Clock}});
    EXPECT_EQ(mod.get_port("a")->type, PortType::Clock);
    ASSERT_ANY_THROW(
        Module::from_verilog(&c, "module1.sv", "module1", {}, {{"aa", PortType::Clock}}));
}

TEST(module, port) {  // NOLINT
    Context c;
    auto mod = c.module("module");
    mod.port(PortDirection::In, "in", 1);
    mod.port(PortDirection::Out, "out", 1);
}

TEST(module, expr) {  // NOLINT
    Context c;
    auto mod = c.module("module");
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
}