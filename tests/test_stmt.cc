#include "../src/context.hh"
#include "../src/generator.hh"
#include "../src/stmt.hh"
#include "gtest/gtest.h"

TEST(stmt, assign) {  // NOLINT
    Context c;
    auto &mod = c.generator("test");
    auto &var1 = mod.var("a", 2);
    auto &var2 = mod.var("b", 2, true);
    auto &var3 = mod.var("c", 4);
    auto &var4 = mod.var("d", 4);
    EXPECT_ANY_THROW(var1.assign(var2));
    EXPECT_ANY_THROW(var1.assign(var3));
    auto &stmt = var4.assign(var3);
    mod.add_stmt(stmt.shared_from_this());
    EXPECT_EQ(mod.stmts_count(), 1);
    auto stmt_ptr = mod.get_stmt(0)->as<AssignStmt>();
    EXPECT_EQ(stmt_ptr, stmt.shared_from_this());

    // test SSA
    EXPECT_EQ(var3.assign(var4), var3.assign(var4));

    // try slice assign
    EXPECT_NO_THROW(var1.assign(var3[{1, 0}]));

    // duplicated yet wrong assignment
    var3.assign(var4, AssignmentType::Blocking);
    EXPECT_ANY_THROW(var3.assign(var4, AssignmentType::NonBlocking));
}

TEST(stmt, if_stmt) {  // NOLINT
    Context c;
    auto &mod = c.generator("test");
    auto &var1 = mod.var("a", 2);
    auto &var2 = mod.var("b", 2);
    auto &var3 = mod.var("c", 4);
    auto &var4 = mod.var("d", 4);
    auto if_ = IfStmt(var1.eq(var2));
    if_.add_then_stmt(var1.assign(var2));
    if_.add_else_stmt(var3.assign(var4));
    EXPECT_EQ(if_.then_body().back(), var1.assign(var2).shared_from_this());
    EXPECT_EQ(if_.else_body().back(), var3.assign(var4).shared_from_this());
}

TEST(stmt, block) {  // NOLINT
    Context c;
    auto &mod = c.generator("test");
    auto &var1 = mod.var("a", 2);
    auto &var2 = mod.var("b", 2);
    auto &var3 = mod.var("c", 4);
    auto &var4 = mod.var("d", 4);
    auto &clk = mod.port(PortDirection::In, "clk", 1, PortType::Clock, false);
    //
    auto seq_block = SequentialStmtBlock();
    seq_block.add_statement(var1.assign(var2));
    // error checking
    EXPECT_ANY_THROW(seq_block.add_statement(var1.assign(var2, AssignmentType::Blocking)));
    EXPECT_ANY_THROW(seq_block.add_statement(var3.assign(var4, AssignmentType::Blocking)));
    auto comb_block = CombinationalStmtBlock();
    comb_block.add_statement(var3.assign(var4));
    EXPECT_EQ(var3.assign(var4).assign_type(), AssignmentType::Blocking);
    EXPECT_NO_THROW(seq_block.add_condition({BlockEdgeType::Posedge, clk.shared_from_this()}));
    EXPECT_ANY_THROW(seq_block.add_condition({BlockEdgeType::Posedge, var1.shared_from_this()}));
    EXPECT_EQ(seq_block.get_conditions().size(), 1);
}