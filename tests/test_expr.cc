#include "../src/except.hh"
#include "../src/expr.hh"
#include "../src/generator.hh"
#include "../src/stmt.hh"
#include "../src/debug.hh"
#include "gtest/gtest.h"

using namespace kratos;

TEST(expr, arith) {  // NOLINT
    Context c;
    auto mod = c.generator("mod");
    Port &p_in = mod.port(PortDirection::In, "in", 1);
    Port &p_out = mod.port(PortDirection::Out, "out", 1);

    Var &var1 = mod.var("a", 1);
    Var &var2 = mod.var("b", 1);
    auto &expr = var1 + var2;
    EXPECT_EQ(expr.left, &var1);

    expr = p_in + p_out;
    EXPECT_EQ(expr.to_string(), "in + out");

    expr = (var1 - var2).ashr(var2);
    EXPECT_EQ(expr.to_string(), "(a - b) >>> b");

    // test expr to expr
    expr = var1 - var2;
    auto &expr_ = expr + expr;
    EXPECT_EQ(expr_.to_string(), "(a - b) + (a - b)");

    // logical and and or
    expr = var1 && var2;
    EXPECT_EQ(expr.to_string(), "a && b");
    expr = var1 || var2;
    EXPECT_EQ(expr.to_string(), "a || b");

    // test unary
    auto &expr_unary = -var1;
    EXPECT_EQ(expr_unary.to_string(), "-a");

    // test raw expr
    // we have to use the reference version to use shared_from_this
    Var &var3 = mod.var("c", 1);
    expr = Expr(ExprOp::Add, &var1, &var3);
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
    auto mod = c.generator("mod");

    auto &var1 = mod.var("a", 2);
    auto &var2 = mod.var("b", 2);
    auto &exp = var1 >= var2;
    EXPECT_EQ(exp.width(), 1);
}

TEST(expr, assign) {  // NOLINT
    Context c;
    auto mod = c.generator("mod");

    auto &var1 = mod.var("a", 1);
    auto &var2 = mod.var("b", 1);
    auto &var3 = mod.var("c", 1);
    auto &var4 = var1 + var2;
    auto assign_stmt = var3.assign(var4);
    EXPECT_EQ(assign_stmt->right(), &var4);
    EXPECT_EQ(assign_stmt->left(), &var3);
    // commit the assignment
    mod.add_stmt(assign_stmt);
    EXPECT_TRUE(var3.sources().find(assign_stmt) != var3.sources().end());
    auto raw_stmt = AssignStmt(var3.shared_from_this(), var4.shared_from_this());
    EXPECT_EQ(raw_stmt.left(), assign_stmt->left());
}

TEST(expr, const_val) {  // NOLINT
    Context c;
    auto mod = c.generator("mod");
    auto &c0 = constant(10, 4);
    EXPECT_ANY_THROW(constant(10, 4, true));
    auto &c1 = constant(-4, 4, true);
    EXPECT_EQ(c0.to_string(), "4'hA");
    EXPECT_EQ(c1.to_string(), "-4'h4");
}

TEST(expr, concat) {  // NOLINT
    Context c;
    auto mod = c.generator("mod");
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
    auto mod = c.generator("mod");
    auto p = Param(&mod, "a", 2, false);
    auto value = 2;
    p.set_value(value);
    EXPECT_EQ(p.to_string(), "a");
    EXPECT_EQ(p.value(), value);
    EXPECT_EQ(p.value_str(), "2'h2");
}

TEST(expr, port_packed) {  // NOLINT
    Context c;
    auto mod = c.generator("mod");
    auto struct_ = PackedStruct("data", {{"value1", 1, false}, {"value2", 2, false}});
    auto port = PortPackedStruct(&mod, PortDirection::In, "in", struct_);

    auto slice1 = PackedSlice(&port, "value2");
    auto &slice2 = port["value2"];

    EXPECT_EQ(slice1.to_string(), "in.value2");
    EXPECT_EQ(slice1.to_string(), slice2.to_string());
    EXPECT_EQ(slice2.low, 1);
    EXPECT_EQ(slice2.high, 2);
}

TEST(expr, array_slice) {  // NOLINT
    Context c;
    auto mod = c.generator("mod");
    auto &array0 = mod.var("t", 4, 3, false);
    auto &slice0 = array0[2];
    EXPECT_EQ(slice0.to_string(), "t[2]");
    EXPECT_EQ(slice0[0].to_string(), "t[2][0]");
}

TEST(expr, ternary) {  // NOLINT
    Context c;
    auto mod = c.generator("mod");
    auto &cond = mod.var("cond", 1);
    auto &a = mod.var("a", 1);
    auto &b = mod.var("b", 1);
    auto result =
        ConditionalExpr(cond.shared_from_this(), a.shared_from_this(), b.shared_from_this());
    EXPECT_EQ(result.to_string(), "cond ? a: b");
}

TEST(expr, unary) {  // NOLINT
    Context c;
    auto mod = c.generator("mod");
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
    auto mod = c.generator("mod");
    auto &a = mod.var("a", 16, 4);
    auto &b = mod.var("b", 2);
    auto &slice = a[b.shared_from_this()];
    EXPECT_EQ(slice.to_string(), "a[b]");
}

TEST(expr, keyword) {  // NOLINT
    Context c;
    auto mod = c.generator("mod");

    EXPECT_THROW(mod.var("var", 1), UserException);
}

TEST(expr, handle_name) {  // NOLINT
    Context c;
    auto &mod1 = c.generator("mod1");
    auto &mod2 = c.generator("mod2");
    mod1.add_child_generator("mod", mod2.shared_from_this());
    auto &var = mod2.var("var_", 1);
    EXPECT_EQ(var.handle_name(), "mod1.mod.var_");
}

TEST(expr, param_width) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod1");
    auto &param = mod.parameter("WIDTH", 4);
    param.set_value(4);
    auto &p = mod.port(PortDirection::In, "in", 2);
    EXPECT_NO_THROW(p.set_width_param(param.as<Param>()));
    EXPECT_EQ(p.width(), 4);
}

TEST(expr, handle_name_gen) {  // NOLINT
    Context c;
    auto &mod1 = c.generator("mod1");
    auto &mod2 = c.generator("mod2");
    mod1.add_child_generator("mod", mod2.shared_from_this());
    auto &var = mod2.var("var_", 1);
    EXPECT_EQ(var.handle_name(&mod2), "var_");
    EXPECT_EQ(var.handle_name(&mod1), "mod.var_");
}

TEST(expr, invert_slice) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");
    auto &a = mod.var("a", 2);
    auto &b = ~(a[1]);
    EXPECT_EQ(b.to_string(), "~a[1]");
}

TEST(expr, reduction) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");
    auto &a = mod.var("a", 2);
    auto &b = a.r_or();
    EXPECT_EQ(b.width(), 1);
    EXPECT_EQ(b.to_string(), "|a");
}

TEST(expr, move_src) {  // NOLINT
    Context context;
    auto &mod = context.generator("mod");
    auto &a = mod.var("a", 2);
    auto &b = mod.var("b", 2);
    auto &c = mod.var("c", 2);
    auto &d = mod.var("d", 2);
    auto stmt = a[0].assign(b[0]);
    mod.add_stmt(stmt);
    Var::move_src_to(&a, &c, &mod, false);
    Var::move_sink_to(&b, &d, &mod, false);
    EXPECT_EQ(stmt->left()->to_string(), "c[0]");
    EXPECT_EQ(stmt->right()->to_string(), "d[0]");
}

TEST(expr, extract_source) {  // NOLINT
    Context context;
    auto &mod = context.generator("mod");
    auto &a = mod.var("a", 8);
    auto &b = mod.var("b", 2);
    auto &c = mod.var("c", 2);
    auto &d = mod.var("d", 2);
    auto &e = mod.var("e", 2);
    auto &f = mod.var("f", 4);
    mod.add_stmt(a.assign(b.concat(c).concat(d).concat(e + d)));
    mod.add_stmt(f.assign(c.concat(e + d[0].concat(d[1]))));
    auto result = find_driver_signal(&mod);
    EXPECT_EQ(result.size(), 2);
    EXPECT_TRUE(result.find(&a) != result.end());
    auto sources = result.at(&a);
    EXPECT_EQ(sources.size(), 4);
    EXPECT_TRUE(result.find(&f) != result.end());
    sources = result.at(&f);
    EXPECT_EQ(sources.size(), 2);
}

TEST(expr, extend) {    // NOLINT
    auto &a = constant(4, 4).extend(8);
    EXPECT_EQ(a.to_string(), "8'(4'h4)");
}

TEST(expr, md_array) {    // NOLINT
    Context context;
    auto &mod = context.generator("mod");
    auto &a = mod.var("a", 16, {4, 2});
    EXPECT_EQ(a.size()[0], 4);
    EXPECT_EQ(a.size()[1], 2);
    auto &b = mod.var("b", 16, {4, 2});
    auto &c = mod.var("c", 16, {4, 2});
    b.set_is_packed(true);
    c.set_is_packed(true);
    // mixture packed and unpacked
    EXPECT_THROW(a.assign(b), StmtException);
    EXPECT_THROW(a[0].assign(b[0]), StmtException);
    EXPECT_NO_THROW(a[0][0].assign(b[0][0]));
    auto &slice = b[{1, 0}];
    EXPECT_EQ(slice.size()[1], 2);
    EXPECT_NO_THROW((b[{1, 0}].assign(c[{1, 0}])));
}

TEST(expr, bit_slice) { // NOLINT
    Context context;
    auto &mod = context.generator("mod");
    auto &array = mod.var("array", 2, 2);
    auto &v_0 = array[0][0];
    EXPECT_EQ(v_0.var_high(), 0);
    EXPECT_EQ(v_0.var_low(), 0);

    auto &v_1 = array[0][1];
    EXPECT_EQ(v_1.var_high(), 1);
    EXPECT_EQ(v_1.var_low(), 1);
}