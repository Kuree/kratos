#include "../src/codegen.hh"
#include "../src/context.hh"
#include "../src/except.hh"
#include "../src/generator.hh"
#include "../src/stmt.hh"
#include "../src/util.hh"
#include "gtest/gtest.h"

using namespace kratos;

TEST(stmt, assign) {  // NOLINT
    Context c;
    auto &mod = c.generator("test");
    auto &var1 = mod.var("a", 2);
    auto &var2 = mod.var("b", 2, 1, true);
    auto &var3 = mod.var("c", 4);
    auto &var4 = mod.var("d", 4);
    EXPECT_THROW(var1.assign(var2), VarException);
    EXPECT_THROW(var1.assign(var3), VarException);
    auto stmt = var4.assign(var3);
    mod.add_stmt(stmt);
    EXPECT_EQ(mod.stmts_count(), 1);
    auto stmt_ptr = mod.get_stmt(0)->as<AssignStmt>();
    EXPECT_EQ(stmt_ptr, stmt);

    // try slice assign
    EXPECT_NO_THROW(var1.assign(var3[{1, 0}]));
}

TEST(stmt, if_stmt) {  // NOLINT
    Context c;
    auto &mod = c.generator("test");
    auto &var1 = mod.var("a", 2);
    auto &var2 = mod.var("b", 2);
    auto &var3 = mod.var("c", 4);
    auto &var4 = mod.var("d", 4);
    auto if_ = IfStmt(var1.eq(var2));
    auto stmt1 = var1.assign(var2);
    if_.add_then_stmt(stmt1);
    auto stmt2 = var3.assign(var4);
    if_.add_else_stmt(stmt2);
    EXPECT_EQ(if_.then_body()->back(), stmt1);
    EXPECT_EQ(if_.else_body()->back(), stmt2);
}

TEST(stmt, block) {  // NOLINT
    Context c;
    auto &mod = c.generator("test");
    auto &var1 = mod.var("a", 2);
    auto &var2 = mod.var("b", 2);
    auto &var3 = mod.var("c", 4);
    auto &var4 = mod.var("d", 4);
    auto &clk = mod.port(PortDirection::In, "clk", 1, 1, PortType::Clock, false);
    //
    auto seq_block = SequentialStmtBlock();
    seq_block.add_stmt(var1.assign(var2));
    // error checking
    EXPECT_THROW(seq_block.add_stmt(var1.assign(var2, AssignmentType::Blocking)), StmtException);
    auto stmt = var3.assign(var4, AssignmentType::Blocking);
    EXPECT_THROW(seq_block.add_stmt(stmt), StmtException);
    auto comb_block = CombinationalStmtBlock();
    comb_block.add_stmt(var3.assign(var4));
    EXPECT_EQ(stmt->assign_type(), AssignmentType::Blocking);
    EXPECT_NO_THROW(seq_block.add_condition({BlockEdgeType::Posedge, clk.shared_from_this()}));
    EXPECT_EQ(seq_block.get_conditions().size(), 1);
}

TEST(stmt, switch_) {  // NOLINT
    Context c;
    auto &mod = c.generator("test");
    auto &var1 = mod.var("a", 2);
    auto &var2 = mod.var("b", 2);
    auto &var3 = mod.var("c", 4);
    auto &var4 = mod.var("d", 4);

    auto switch_block = SwitchStmt(var1.shared_from_this());
    auto &condition1 = constant(0, 3);
    auto &condition2 = constant(1, 3);
    auto stmt = var1.assign(var2);
    switch_block.add_switch_case(condition1.as<Const>(), stmt);
    switch_block.add_switch_case(condition2.as<Const>(), var3.assign(var4));

    EXPECT_EQ(switch_block.body().size(), 2);
    EXPECT_EQ(switch_block.target(), var1.shared_from_this());
    EXPECT_THROW(switch_block.add_switch_case(condition1.as<Const>(), stmt), StmtException);
}

TEST(stmt, stmt_removal) {  // NOLINT
    Context c;
    auto &mod = c.generator("test");
    auto &var1 = mod.var("a", 1);
    auto &var2 = mod.var("b", 1);
    auto comb = mod.combinational();
    auto if_stmt = std::make_shared<IfStmt>(var1);
    if_stmt->add_then_stmt(var2.assign(var1));
    auto switch_stmt = std::make_shared<SwitchStmt>(var1);
    auto stmt = var2.assign(var1);
    auto case_ = constant(1, 1).as<Const>();
    switch_stmt->add_switch_case(case_, stmt);

    // remove stmt
    remove_stmt_from_parent(if_stmt->then_body()->get_stmt(0));
    EXPECT_TRUE(if_stmt->then_body()->empty());
    remove_stmt_from_parent(stmt);
    EXPECT_TRUE(switch_stmt->body().at(case_)->empty());
    remove_stmt_from_parent(if_stmt);
    remove_stmt_from_parent(switch_stmt);
    EXPECT_EQ(comb->size(), 0);
}

TEST(stmt, for_loop) {  // NOLINT
    Context c;
    auto &mod = c.generator("test");
    auto &var1 = mod.var("a", 4, 8);
    auto comb = mod.combinational();
    auto loop = std::make_shared<ForStmt>("i", 0, 4, 1);
    comb->add_stmt(loop);
    auto iter = loop->get_iter_var();
    std::shared_ptr<AssignStmt> stmt;
    EXPECT_NO_THROW(stmt = var1[iter].assign(iter, AssignmentType::Blocking));
    loop->add_stmt(stmt);

    SystemVerilogCodeGen codegen(&mod);
    auto result = codegen.str();
    EXPECT_TRUE(result.find("for (int unsigned i = 0; i < 4; i += 1) begin") != std::string::npos);
    EXPECT_TRUE(result.find("a[3'(i)] = 4'(i);") != std::string::npos);
}

TEST(stmt, clone) { // NOLINT
    Context c;
    auto &mod = c.generator("mod");
    auto &a = mod.var("a", 1);
    auto &b = mod.var("b", 1);
    auto &c_ = mod.var("c", 1);
    auto &d = mod.var("d", 1);
    auto &e = mod.var("e", 16);

    // assign
    auto stmt_assign = a.assign(b);
    auto stmt_assign_clone = stmt_assign->clone()->as<AssignStmt>();
    EXPECT_EQ(stmt_assign_clone->left(), &a);
    EXPECT_EQ(stmt_assign_clone->right(), &b);
    EXPECT_NE(stmt_assign, stmt_assign_clone);

    // if
    auto if_ = std::make_shared<IfStmt>(c_);
    if_->add_then_stmt(a.assign(b));
    if_->add_else_stmt(c_.assign(d));
    auto if_cloned = if_->clone()->as<IfStmt>();
    EXPECT_EQ(if_cloned->predicate(), if_->predicate());
    // the assignment should be cloned
    EXPECT_NE(if_cloned->then_body()->get_stmt(0), if_->then_body()->get_stmt(0));
    EXPECT_NE(if_cloned->else_body()->get_stmt(0), if_->else_body()->get_stmt(0));
    EXPECT_EQ(if_cloned->then_body()->parent(), if_cloned.get());
    EXPECT_EQ(if_cloned->then_body()->get_stmt(0)->parent(), if_cloned->then_body().get());

    // case
    auto case_ = std::make_shared<SwitchStmt>(b);
    case_->add_switch_case(constant(1, 1), d.assign(a));
    case_->add_switch_case(nullptr, a.assign(d));
    auto case_clone = case_->clone()->as<SwitchStmt>();
    EXPECT_EQ(case_clone->target(), case_->target());
    auto case_body = case_->body();
    auto case_clone_body = case_clone->body();
    EXPECT_EQ(case_clone_body.size(), case_body.size());
    for (auto const &[cond, stmts]: case_body) {
        EXPECT_TRUE(case_clone_body.find(cond) != case_clone_body.end());
        auto stmts_cloned = case_clone_body.at(cond);
        EXPECT_EQ(stmts_cloned->size(), stmts->size());
        EXPECT_EQ(stmts_cloned->parent(), case_clone.get());
        auto assign = stmts->get_stmt(0)->as<AssignStmt>();
        auto assign_cloned = stmts_cloned->get_stmt(0)->as<AssignStmt>();
        EXPECT_EQ(assign->left(), assign_cloned->left());
        EXPECT_EQ(assign->right(), assign_cloned->right());
        EXPECT_EQ(assign_cloned->parent(), stmts_cloned.get());
    }

    // for
    auto for_ = std::make_shared<ForStmt>("i", 0, 42, 1);
    for_->add_stmt(e.assign(for_->get_iter_var()));
    auto for_cloned = for_->clone()->as<ForStmt>();
    EXPECT_EQ(for_->step(), for_cloned->step());
    EXPECT_EQ(for_->start(), for_cloned->start());
    EXPECT_EQ(for_->end(), for_cloned->end());
    auto for_body = for_->get_loop_body();
    auto for_clone_body = for_cloned->get_loop_body();
    EXPECT_EQ(for_body->size(), for_clone_body->size());
    auto for_assign = for_body->get_stmt(0)->as<AssignStmt>();
    auto for_clone_assign = for_clone_body->get_stmt(0)->as<AssignStmt>();
    EXPECT_EQ(for_assign->left(), for_clone_assign->left());
    EXPECT_EQ(for_clone_assign->parent(), for_clone_body.get());
    EXPECT_EQ(for_clone_body->parent(), for_cloned.get());

    // combinational
    auto comb = mod.combinational();
    comb->add_stmt(a.assign(b));
    auto comb_cloned = comb->clone()->as<CombinationalStmtBlock>();
    EXPECT_EQ(comb_cloned->size(), comb->size());
    auto assign = comb_cloned->get_stmt(0)->as<AssignStmt>();
    EXPECT_EQ(assign->parent(), comb_cloned.get());

    // sequential
    auto seq = mod.sequential();
    seq->add_condition({BlockEdgeType::Negedge, a.shared_from_this()});
    seq->add_stmt(b.assign(c_));
    auto seq_cloned = seq->clone()->as<SequentialStmtBlock>();
    EXPECT_EQ(seq->get_conditions(), seq_cloned->get_conditions());
    EXPECT_EQ(seq_cloned->get_stmt(0)->parent(), seq_cloned.get());

    // latch
    auto latch = mod.latch();
    latch->add_stmt(a.assign(b));
    auto latch_cloned = latch->clone()->as<LatchStmtBlock>();
    EXPECT_EQ(latch_cloned->size(), latch->size());

    // comment
    auto comment = std::make_shared<CommentStmt>("42");
    auto comment_cloned = comment->clone()->as<CommentStmt>();
    EXPECT_EQ(comment->comments(), comment_cloned->comments());

    // raw string
    auto raw_string = std::make_shared<RawStringStmt>("42");
    auto raw_string_cloned = raw_string->clone()->as<RawStringStmt>();
    EXPECT_EQ(raw_string->stmts()[0], raw_string_cloned->stmts()[0]);

}