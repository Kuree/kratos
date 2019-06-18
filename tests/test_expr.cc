#include "../src/expr.hh"
#include "../src/generator.hh"
#include "gtest/gtest.h"

TEST(expr, arith) {  // NOLINT
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

    // test raw expr
    expr = Expr(ExprOp::Add, var1.shared_from_this(), var2.shared_from_this());
    EXPECT_EQ(expr.generator, &mod);
    EXPECT_EQ(expr.name, "(a + b)");
}

TEST(expr, assign) {  // NOLINT
    Context c;
    auto mod = c.generator("module");

    auto &var1 = mod.var("a", 1);
    auto &var2 = mod.var("b", 1);
    auto &var3 = mod.var("c", 1);
    auto &var4 = var1 + var2;
    var3.assign(var4);
    EXPECT_EQ(var3.src(), var4.shared_from_this());
    EXPECT_TRUE(var4.sinks().find(var3.shared_from_this()) != var4.sinks().end());
}