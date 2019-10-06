#include "../src/expr.hh"
#include "../src/generator.hh"
#include "../src/stmt.hh"
#include "gtest/gtest.h"
#include "../src/except.hh"

using namespace kratos;

TEST(expr, arith) {  // NOLINT
    Context c;
    auto mod = c.generator("module");
    Port &p_in = mod.port(PortDirection::In, "in", 1);
    Port &p_out = mod.port(PortDirection::Out, "out", 1);

    Var &var1 = mod.var("a", 1);
    Var &var2 = mod.var("b", 1);
    auto &expr = var1 + var2;
    EXPECT_EQ(expr.left.get(), &var1);

    expr = p_in + p_out;
    EXPECT_EQ(expr.to_string(), "in + out");

    expr = (var1 - var2).ashr(var2);
    EXPECT_EQ(expr.to_string(), "(a - b) >>> b");

    // test expr to expr
    expr = var1 - var2;
    auto &expr_ = expr + expr;
    EXPECT_EQ(expr_.to_string(), "(a - b) + (a - b)");

    // test unary
    auto &expr_unary = -var1;
    EXPECT_EQ(expr_unary.to_string(), "-a");

    // test raw expr
    // we have to use the reference version to use shared_from_this
    Var &var3 = mod.var("c", 1);
    expr = Expr(ExprOp::Add, var1.shared_from_this(), var3.shared_from_this());
    EXPECT_EQ(expr.generator, &mod);

    // test to_string
    EXPECT_EQ(var1.to_string(), "a");
    EXPECT_EQ(expr.to_string(), "a + c");

    // test slice
    Var &wire = mod.var("d", 4);
    auto &slice_expr = wire[{2, 0}];
    EXPECT_EQ(slice_expr.parent_var, wire.shared_from_this().get());
    EXPECT_EQ(slice_expr.high, 2);
    EXPECT_EQ(slice_expr.low, 0);
    EXPECT_EQ(slice_expr.to_string(), "d[2:0]");
    // test the raw interface. users should not do that
    EXPECT_EQ(VarSlice(&wire, 2, 1).width(), 2);

    // test other ops
    EXPECT_EQ((var1.eq(var3)).to_string(), "a == c");
    EXPECT_EQ(var1.cast(VarCastType::Signed)->to_string(), "signed'(a)");
    EXPECT_EQ(VarCasted(&var1, VarCastType::Signed).to_string(), "signed'(a)");
    EXPECT_TRUE(var1.cast(VarCastType::Signed)->is_signed());

    // test pretty print of expr
    expr = var1 + var1 + var2;
    EXPECT_EQ(expr.to_string(), "a + a + b");
    expr = (var1 + var1) - var2;
    EXPECT_EQ(expr.to_string(), "(a + a) - b");
}

TEST(expr, relational) {  // NOLINT
    Context c;
    auto mod = c.generator("module");

    auto &var1 = mod.var("a", 2);
    auto &var2 = mod.var("b", 2);
    auto &exp = var1 >= var2;
    EXPECT_EQ(exp.width(), 1);
}

TEST(expr, assign) {  // NOLINT
    Context c;
    auto mod = c.generator("module");

    auto &var1 = mod.var("a", 1);
    auto &var2 = mod.var("b", 1);
    auto &var3 = mod.var("c", 1);
    auto &var4 = var1 + var2;
    auto assign_stmt = var3.assign(var4);
    EXPECT_EQ(assign_stmt->right(), var4.shared_from_this());
    EXPECT_EQ(assign_stmt->left(), var3.shared_from_this());
    // commit the assignment
    mod.add_stmt(assign_stmt);
    EXPECT_TRUE(var3.sources().find(assign_stmt) != var3.sources().end());
    auto raw_stmt = AssignStmt(var3.shared_from_this(), var4.shared_from_this());
    EXPECT_EQ(raw_stmt.left(), assign_stmt->left());
}

TEST(expr, const_val) {  // NOLINT
    Context c;
    auto mod = c.generator("module");
    auto &c0 = constant(10, 4);
    EXPECT_ANY_THROW(constant(10, 4, true));
    auto &c1 = constant(-4, 4, true);
    EXPECT_EQ(c0.to_string(), "4'hA");
    EXPECT_EQ(c1.to_string(), "-4'h4");
}

TEST(expr, concat) {  // NOLINT
    Context c;
    auto mod = c.generator("module");
    auto &var1 = mod.var("a", 1);
    auto &var2 = mod.var("b", 1);
    auto &var3 = var1.concat(var2);
    auto &var3_ = var3.concat(var2);
    EXPECT_EQ(var3_.to_string(), "{a, b, b}");

    // test raw constructor
    const auto &concat = VarConcat(var1.shared_from_this(), var2.shared_from_this());
    EXPECT_EQ(concat.to_string(), var3.to_string());
}

TEST(expr, param) {  // NOLINT
    Context c;
    auto mod = c.generator("module");
    auto p = Param(&mod, "a", 2, false);
    auto value = 2;
    p.set_value(value);
    EXPECT_EQ(p.to_string(), "a");
    EXPECT_EQ(p.value(), value);
    EXPECT_EQ(p.value_str(), "2'h2");
}

TEST(expr, port_packed) {  // NOLINT
    Context c;
    auto mod = c.generator("module");
    auto struct_ = PackedStruct("data", {{"value1", 1, false}, {"value2", 2, false}});
    auto port = PortPacked(&mod, PortDirection::In, "in", struct_);

    auto slice1 = PackedSlice(&port, "value2");
    auto &slice2 = port["value2"];

    EXPECT_EQ(slice1.to_string(), "in.value2");
    EXPECT_EQ(slice1.to_string(), slice2.to_string());
    EXPECT_EQ(slice2.low, 1);
    EXPECT_EQ(slice2.high, 2);
}

TEST(expr, array_slice) {  // NOLINT
    Context c;
    auto mod = c.generator("module");
    auto &array0 = mod.var("t", 4, 3, false);
    auto &slice0 = array0[2];
    EXPECT_EQ(slice0.to_string(), "t[2]");
    EXPECT_EQ(slice0[0].to_string(), "t[2][0]");
}

TEST(expr, ternary) {  // NOLINT
    Context c;
    auto mod = c.generator("module");
    auto &cond = mod.var("cond", 1);
    auto &a = mod.var("a", 1);
    auto &b = mod.var("b", 1);
    auto result =
        ConditionalExpr(cond.shared_from_this(), a.shared_from_this(), b.shared_from_this());
    EXPECT_EQ(result.to_string(), "cond ? a: b");
}

TEST(expr, unary) {  // NOLINT
    Context c;
    auto mod = c.generator("module");
    auto &a = mod.var("a", 1);
    auto &b = mod.var("b", 1);
    EXPECT_EQ(a.r_or().to_string(), "|a");
    EXPECT_EQ(a.r_and().to_string(), "&a");
    EXPECT_EQ(a.r_xor().to_string(), "^a");
    EXPECT_EQ(a.r_not().to_string(), "!a");
    EXPECT_EQ((b + a.r_or()).to_string(), "b + (|a)");
}

TEST(expr, slice_by_var) {  // NOLINT
    Context c;
    auto mod = c.generator("module");
    auto &a = mod.var("a", 16, 4);
    auto &b = mod.var("b", 2);
    auto &slice = a[b.shared_from_this()];
    EXPECT_EQ(slice.to_string(), "a[b]");
}

TEST(expr, keyword) {   // NOLINT
    Context c;
    auto mod = c.generator("module");

    EXPECT_THROW(mod.var("var", 1), UserException);
}

TEST(expr, handle_name) {   // NOLINT
    Context c;
    auto &mod1 = c.generator("mod1");
    auto &mod2 = c.generator("mod2");
    mod1.add_child_generator("mod", mod2.shared_from_this());
    auto &var = mod2.var("var_", 1);
    EXPECT_EQ(var.handle_name(), "mod1.mod.var_");

}

TEST(expr, param_width) {   // NOLINT
    Context c;
    auto &mod = c.generator("mod1");
    auto &param = mod.parameter("WIDTH", 4);
    param.set_value(4);
    auto &p = mod.port(PortDirection::In, "in", 2);
    EXPECT_NO_THROW(p.set_width_param(param.as<Param>()));
    EXPECT_EQ(p.width(), 4);
}