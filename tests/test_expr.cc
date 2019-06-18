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
    // we have to use the reference version to use shared_from_this
    Var &var3 = mod.var("c", 1);
    expr = Expr(ExprOp::Add, var1.shared_from_this(), var3.shared_from_this());
    EXPECT_EQ(expr.generator, &mod);
    EXPECT_EQ(expr.name, "(a + c)");

    // test to_string
    EXPECT_EQ(var1.to_string(), "a");
    EXPECT_EQ(expr.to_string(), "a + c");

    // test slice
    Var &wire = mod.var("d", 4);
    auto slice_expr = wire[{2, 0}];
    EXPECT_EQ(slice_expr.parent, wire.shared_from_this().get());
    EXPECT_EQ(slice_expr.high, 2);
    EXPECT_EQ(slice_expr.low, 0);
    EXPECT_EQ(slice_expr.name, "d[2:0]");

    // test other ops
    EXPECT_EQ((var1.eq(var3)).to_string(), "a == c");
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