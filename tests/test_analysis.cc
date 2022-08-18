#include "../src/codegen.hh"
#include "../src/except.hh"
#include "../src/fsm.hh"
#include "../src/generator.hh"
#include "../src/interface.hh"
#include "../src/util.hh"
#include "gtest/gtest.h"

using namespace kratos;

TEST(pass, mixed_assignment) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");
    auto &a = mod.var("a", 1);
    auto &b = mod.var("b", 1);
    mod.add_stmt(a.assign(b));
    auto seq = std::make_shared<SequentialStmtBlock>();
    seq->add_stmt(b.assign(constant(1, 1)));
    mod.add_stmt(seq);
    mod.add_stmt(b.assign(constant(1, 1)));

    fix_assignment_type(&mod);
    EXPECT_THROW(check_mixed_assignment(&mod), StmtException);
}

TEST(pass, non_synthesizable) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");
    auto comb = mod.combinational();
    auto dpi = mod.dpi_function("test_dpi");
    auto &call = mod.call("test_dpi", std::map<std::string, std::shared_ptr<Var>>{});
    auto stmt = std::make_shared<FunctionCallStmt>(call.as<FunctionCallVar>());
    comb->add_stmt(stmt);
    // add debug info
    stmt->fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));

    // run the pass
    EXPECT_THROW(check_non_synthesizable_content(&mod), UserException);
}

TEST(pass, check_active_high) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");
    auto &rst = mod.port(PortDirection::In, "reset", 1, 1, PortType::AsyncReset, false);
    auto seq = mod.sequential();
    rst.set_active_high(true);
    seq->add_condition({EventEdgeType::Negedge, rst.shared_from_this()});
    EXPECT_THROW(check_active_high(&mod), VarException);
}

TEST(pass, check_function_return) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");
    auto func = mod.function("test_func");
    auto a = func->input("a", 1, false);
    auto b = func->input("b", 1, false);
    func->add_stmt(func->return_stmt(a));
    func->add_stmt(func->return_stmt(b));

    EXPECT_THROW(check_function_return(&mod), StmtException);
    // clear the statements
    func->clear();
    func->add_stmt(func->return_stmt(a));
    EXPECT_NO_THROW(check_function_return(&mod));
    // clear the statements
    func->clear();
    func->add_stmt(a->assign(constant(1, 1)));
    func->add_stmt(func->return_stmt(b));
    EXPECT_NO_THROW(check_function_return(&mod));
}

TEST(pass, latch) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");
    auto &in = mod.port(PortDirection::In, "in", 2);
    auto &out = mod.port(PortDirection::Out, "out", 1);
    auto &out2 = mod.port(PortDirection::Out, "out2", 1);
    auto comb = mod.combinational();

    auto switch_stmt = std::make_shared<SwitchStmt>(in.shared_from_this());
    switch_stmt->add_switch_case(constant(0, 2).as<Const>(), out2.assign(constant(0, 1)));
    switch_stmt->add_switch_case(nullptr, out2.assign(constant(1, 1)));

    comb->add_stmt(switch_stmt);

    EXPECT_NO_THROW(check_inferred_latch(&mod));

    auto if_stmt = std::make_shared<IfStmt>(in.eq(constant(0, 2)));
    if_stmt->add_then_stmt(out.assign(constant(0, 1)));
    comb->add_stmt(if_stmt);

    EXPECT_THROW(check_inferred_latch(&mod), StmtException);
}

TEST(pass, latch_rst) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");
    auto &in = mod.port(PortDirection::In, "in", 1);
    auto &out = mod.port(PortDirection::Out, "out", 1);
    auto &clk = mod.port(PortDirection::In, "clk", 1, 1, PortType::Clock, false);
    auto &rst = mod.port(PortDirection::In, "rst", 1, 1, PortType::AsyncReset, false);
    auto &cen = mod.port(PortDirection::In, "cen", 1, 1, PortType::ClockEnable, false);

    auto seq = mod.sequential();
    seq->add_condition({EventEdgeType::Posedge, clk.shared_from_this()});
    seq->add_condition({EventEdgeType::Posedge, rst.shared_from_this()});
    auto if_ = std::make_shared<IfStmt>(rst);
    if_->add_then_stmt(out.assign(constant(0, 1)));
    auto if_2 = std::make_shared<IfStmt>(cen);
    if_2->add_then_stmt(out.assign(in));
    if_->add_else_stmt(if_2);
    seq->add_stmt(if_);

    EXPECT_NO_THROW(check_inferred_latch(&mod));
}

TEST(pass, check_combinational_loop) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");
    auto &a = mod.var("a", 1);
    mod.add_stmt(a.assign(a + constant(1, 1)));
    fix_assignment_type(&mod);

    EXPECT_THROW(check_combinational_loop(&mod), StmtException);
}

TEST(pass, check_d_flip_flop) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");
    auto &a = mod.var("a", 1);
    auto &b = mod.var("b", 1);
    auto seq = mod.sequential();
    seq->add_stmt(a.assign(constant(1, 1)));
    auto if_ = std::make_shared<IfStmt>(a);
    seq->add_stmt(if_);
    if_->add_then_stmt(b.assign(constant(1, 1)));

    EXPECT_THROW(check_flip_flop_always_ff(&mod), StmtException);
}

TEST(pass, connectivity) {  // NOLINT
    Context c;
    auto &mod1 = c.generator("module1");
    auto &port1 = mod1.port(PortDirection::In, "in", 1);
    auto &port2 = mod1.port(PortDirection::Out, "out", 1);

    EXPECT_THROW(verify_generator_connectivity(&mod1), StmtException);
    mod1.add_stmt(port2.assign(port1));

    EXPECT_NO_THROW(verify_generator_connectivity(&mod1));

    auto &mod2 = c.generator("module2");
    EXPECT_NE(&mod1, &mod2);

    mod1.add_child_generator("inst", mod2.shared_from_this());
    EXPECT_THROW(mod1.port(PortDirection::In, "in", 1), VarException);
    auto &port3 = mod2.port(PortDirection::In, "in", 1);
    mod1.add_stmt(port3.assign(port1));
    EXPECT_NO_THROW(verify_generator_connectivity(&mod1));

    auto &port4 = mod2.port(PortDirection::Out, "out", 1);
    EXPECT_THROW(verify_generator_connectivity(&mod1), StmtException);
    mod2.add_stmt(port4.assign(port3));

    EXPECT_NO_THROW(verify_generator_connectivity(&mod1));
}