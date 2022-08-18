#include "../src/codegen.hh"
#include "../src/except.hh"
#include "../src/fsm.hh"
#include "../src/generator.hh"
#include "../src/interface.hh"
#include "../src/pass.hh"
#include "../src/util.hh"
#include "gtest/gtest.h"

using namespace kratos;

TEST(pass, if_case) {  // NOLINT
    Context c;
    auto &mod = c.generator("module1");
    auto &in = mod.port(PortDirection::In, "in", 3);
    auto &out = mod.port(PortDirection::Out, "out", 3);
    auto if_stmt = std::make_shared<IfStmt>(in.eq(constant(0, 3)));
    if_stmt->add_then_stmt(out.assign(constant(0, 3)));
    auto if_stmt2 = std::make_shared<IfStmt>(in.eq(constant(1, 3)));
    if_stmt2->add_then_stmt(out.assign(constant(1, 3)));
    if_stmt2->add_else_stmt(out.assign(constant(0, 3)));
    if_stmt->add_else_stmt(if_stmt2);
    auto stmt_list = std::make_shared<CombinationalStmtBlock>();
    stmt_list->add_stmt(if_stmt);
    mod.add_stmt(stmt_list);

    transform_if_to_case(&mod);
    auto *stmt = reinterpret_cast<Stmt *>(mod.get_child(0)->get_child(0));
    EXPECT_TRUE(stmt->type() == StatementType::Switch);
    auto switch_ = stmt->as<SwitchStmt>();
    EXPECT_EQ(switch_->body().size(), 3);
    EXPECT_TRUE(switch_->body().find(nullptr) != switch_->body().end());

    fix_assignment_type(&mod);
    auto result = generate_verilog(&mod);
    EXPECT_TRUE(result.find("module1") != result.end());
}

TEST(pass, merge_if_1) {  // NOLINT
    // this test merge the same if condition
    Context c;
    auto &mod = c.generator("mod");
    auto &a = mod.var("a", 2);
    auto &b = mod.var("b", 2);
    auto comb = mod.combinational();
    auto if_ = std::make_shared<IfStmt>(a.eq(constant(1, 2)));
    auto assign1 = b.assign(constant(1, 2));
    if_->add_then_stmt(assign1);
    auto if2 = std::make_shared<IfStmt>(a.eq(constant(1, 2)));
    auto assign2 = b.assign(constant(1, 2));
    if2->add_then_stmt(assign2);
    comb->add_stmt(if_);
    comb->add_stmt(if2);
    auto attr = std::make_shared<Attribute>();
    attr->value_str = "merge_if_block";
    comb->add_attribute(attr);
    merge_if_block(&mod);
    EXPECT_EQ(comb->size(), 1);
    EXPECT_EQ(comb->get_child(0), if_.get());
    EXPECT_EQ(if_->then_body()->size(), 2);
    EXPECT_EQ(if_->then_body()->get_child(0), assign1.get());
    EXPECT_EQ(if_->then_body()->get_child(1), assign2.get());
}

TEST(pass, merge_if_2) {  // NOLINT
                          // this test merge the same if condition
    Context c;
    auto &mod = c.generator("mod");
    auto &a = mod.var("a", 2);
    auto &b = mod.var("b", 2);
    auto comb = mod.combinational();
    auto if_ = std::make_shared<IfStmt>(a.eq(constant(1, 2)));
    auto assign1 = b.assign(constant(1, 2));
    if_->add_then_stmt(assign1);
    auto if2 = std::make_shared<IfStmt>(a.eq(constant(2, 2)));
    auto assign2 = b.assign(constant(2, 2));
    if2->add_then_stmt(assign2);
    comb->add_stmt(if_);
    comb->add_stmt(if2);
    auto attr = std::make_shared<Attribute>();
    attr->value_str = "merge_if_block";
    comb->add_attribute(attr);
    merge_if_block(&mod);
    EXPECT_EQ(comb->size(), 1);
    EXPECT_EQ(comb->get_child(0), if_.get());
    EXPECT_EQ(if_->then_body()->size(), 1);
    EXPECT_EQ(if_->else_body()->size(), 1);
    EXPECT_EQ(if_->then_body()->get_child(0), assign1.get());
    EXPECT_EQ(if_->else_body()->get_child(0), if2.get());
}

TEST(pass, fanout) {  // NOLINT
    Context c;
    auto &mod = c.generator("module1");
    auto &in = mod.port(PortDirection::In, "in", 3);
    auto &out = mod.port(PortDirection::Out, "out", 3);
    auto &var1 = mod.var("a", 3);
    auto &var2 = mod.var("b", 3);

    mod.add_stmt(var1.assign(in));
    mod.add_stmt(var2.assign(var1));
    mod.add_stmt(out.assign(var2));

    remove_fanout_one_wires(&mod);

    EXPECT_TRUE(var1.sinks().empty());
    EXPECT_TRUE(var1.sources().empty());
    EXPECT_TRUE(var2.sinks().empty());
    EXPECT_TRUE(var2.sources().empty());

    // remove unused variables
    remove_unused_vars(&mod);
    EXPECT_EQ(mod.get_var("a"), nullptr);
    EXPECT_EQ(mod.get_var("b"), nullptr);

    fix_assignment_type(&mod);
    auto mod_src = generate_verilog(&mod);
    auto src = mod_src["module1"];
    EXPECT_TRUE(is_valid_verilog(src));
    EXPECT_TRUE(src.find('b') == std::string::npos);
}

TEST(pass, pass_through_module) {  // NOLINT
    Context c;
    auto &mod1 = c.generator("module1");
    auto &in1 = mod1.port(PortDirection::In, "in", 1);
    auto &out1 = mod1.port(PortDirection::Out, "out", 1);

    auto &mod2 = c.generator("module2");
    auto &in2 = mod2.port(PortDirection::In, "in", 1);
    auto &out2 = mod2.port(PortDirection::Out, "out", 1);
    mod2.add_stmt(out2.assign(in2));

    mod1.add_child_generator("inst0", mod2.shared_from_this());
    mod1.add_stmt(in2.assign(in1));
    mod1.add_stmt(out1.assign(out2));

    remove_pass_through_modules(&mod1);

    EXPECT_TRUE(in2.sources().empty());
    EXPECT_TRUE(out2.sinks().empty());

    EXPECT_EQ(mod1.get_child_generator_size(), 0);
    EXPECT_FALSE(mod1.has_child_generator(mod2.shared_from_this()));

    EXPECT_NO_THROW(verify_generator_connectivity(&mod1));
}

TEST(pass, test_merge_wire_assignment_block) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");
    auto &a = mod.var("a", 4);
    auto &b = mod.var("b", 4);

    auto comb = mod.combinational();
    for (auto i = 0; i < 4; i++) {
        comb->add_stmt(a[i].assign(b[i]));
    }

    fix_assignment_type(&mod);
    merge_wire_assignments(&mod);
    EXPECT_EQ(comb->size(), 1);
}

TEST(pass, insert_clk_en) {  // NOLINT
    Context c;
    auto &parent = c.generator("parent");
    auto &clk = parent.port(PortDirection::In, "clk", 1, PortType::Clock);
    auto &rst = parent.port(PortDirection::In, "rst", 1, PortType::AsyncReset);
    auto &a = parent.port(PortDirection::Out, "a", 1);

    auto seq = parent.sequential();
    seq->add_condition({EventEdgeType::Posedge, clk.shared_from_this()});
    seq->add_condition({EventEdgeType::Posedge, rst.shared_from_this()});
    auto if_ = std::make_shared<IfStmt>(rst);
    if_->add_then_stmt(a.assign(constant(1, 1)));
    if_->add_else_stmt(a.assign(constant(0, 1)));
    seq->add_stmt(if_);

    // add child generator
    auto &child = c.generator("child");
    auto &clk_child = child.port(PortDirection::In, "clk", 1, PortType::Clock);
    auto child_seq = child.sequential();
    child_seq->add_condition({EventEdgeType::Posedge, clk_child.shared_from_this()});
    child_seq->add_stmt(child.var("a", 1).assign(constant(1, 1)));
    child_seq->add_stmt(child.var("b", 1).assign(constant(1, 1)));

    // another child generator
    auto &child2 = c.generator("child2");
    auto &clk_child2 = child2.port(PortDirection::In, "clk", 1, PortType::Clock);
    auto &clk_en_child2 = child2.port(PortDirection::In, "clk_en", 1, PortType::ClockEnable);
    // always const
    child2.wire(clk_en_child2, constant(1, 1));
    auto child_seq2 = child2.sequential();
    child_seq2->add_condition({EventEdgeType::Posedge, clk_child2.shared_from_this()});
    auto if_child2 = std::make_shared<IfStmt>(clk_en_child2);
    if_child2->add_then_stmt(child2.var("a", 1).assign(constant(1, 1)));
    child_seq2->add_stmt(if_child2);

    auto &child3 = c.generator("child3");
    auto &clk_child3 = child3.port(PortDirection::In, "clk", 1, PortType::Clock);
    auto &clk_en_child3 = child3.port(PortDirection::In, "clk_en", 1, PortType::ClockEnable);
    auto child_seq3 = child3.sequential();
    child_seq2->add_condition({EventEdgeType::Posedge, clk_child3.shared_from_this()});
    auto if_child3 = std::make_shared<IfStmt>(clk_en_child3);
    if_child3->add_then_stmt(child3.var("a", 1).assign(constant(1, 1)));
    child_seq3->add_stmt(if_child3);

    parent.add_child_generator("child", child.shared_from_this());
    parent.add_child_generator("child2", child2.shared_from_this());
    parent.add_child_generator("child3", child3.shared_from_this());
    parent.wire(clk_child, clk);
    parent.wire(clk_child2, clk);
    parent.wire(clk_child3, clk);

    // add clock enable
    auto &parent_clk_en = parent.port(PortDirection::In, "clk_en", 1, PortType::ClockEnable);
    // wire it to child3
    parent.wire(clk_en_child3, parent_clk_en);
    auto_insert_clock_enable(&parent);
    fix_assignment_type(&parent);
    create_module_instantiation(&parent);
    auto src = generate_verilog(&parent);
    EXPECT_TRUE(src.find("parent") != src.end());
    EXPECT_TRUE(src.find("child") != src.end());
    EXPECT_TRUE(src.find("child2") != src.end());
    EXPECT_TRUE(src.find("child3") != src.end());
    auto parent_src = src.at("parent");
    auto child_src = src.at("child");
    auto child_src2 = src.at("child2");
    EXPECT_TRUE(parent_src.find("else if (clk_en)") != std::string::npos);
    EXPECT_TRUE(child_src.find("if (clk_en)") != std::string::npos);
    EXPECT_TRUE(child_src2.find("if (clk_en)") != std::string::npos);
}

TEST(pass, insert_sync_reset) {  // NOLINT
    Context c;
    auto &parent = c.generator("parent");
    auto &clk = parent.port(PortDirection::In, "clk", 1, PortType::Clock);
    auto &rst = parent.port(PortDirection::In, "rst", 1, PortType::AsyncReset);
    auto &clk_en = parent.port(PortDirection::In, "clk_en", 1, PortType::ClockEnable);
    auto &a = parent.port(PortDirection::Out, "a", 1);
    auto &b = parent.var("b", 1);
    auto &c_ = parent.var("c", 1);

    // this is the one with reset logic
    {
        auto seq_parent = parent.sequential();
        seq_parent->add_condition({EventEdgeType::Posedge, clk.shared_from_this()});
        auto if_seq_parent = std::make_shared<IfStmt>(rst);
        if_seq_parent->add_then_stmt(b.assign(constant(0, 1)));
        if_seq_parent->add_else_stmt(c_.assign(a));
        seq_parent->add_stmt(if_seq_parent);
    }

    // this is the one with both reset and clock enable
    {
        auto seq_parent = parent.sequential();
        seq_parent->add_condition({EventEdgeType::Posedge, clk.shared_from_this()});
        auto if_seq_parent = std::make_shared<IfStmt>(rst);
        if_seq_parent->add_then_stmt(b.assign(constant(0, 1)));
        auto if_clk_en = std::make_shared<IfStmt>(clk_en);
        if_clk_en->add_then_stmt(c_.assign(a));
        if_seq_parent->add_else_stmt(if_clk_en);
        seq_parent->add_stmt(if_seq_parent);
    }

    // test child wiring
    auto &child = c.generator("child");
    parent.add_child_generator("child", child.shared_from_this());
    auto &clk_child = child.port(PortDirection::In, "clk", 1, PortType::Clock);
    auto &rst_child = child.port(PortDirection::In, "rst", 1, PortType::AsyncReset);
    parent.wire(clk_child, clk);
    parent.wire(rst_child, rst);
    {
        auto &a_child = child.var("a", 1);
        auto &b_child = child.var("b", 1);
        auto &c_child = child.var("c", 1);
        auto seq_child = child.sequential();
        seq_child->add_condition({EventEdgeType::Posedge, clk_child.shared_from_this()});
        // same thing as the parent
        auto if_seq_child = std::make_shared<IfStmt>(rst_child);
        if_seq_child->add_then_stmt(b_child.assign(constant(0, 1)));
        if_seq_child->add_else_stmt(c_child.assign(a_child));
        seq_child->add_stmt(if_seq_child);
    }

    // this child already has it's own flush logic
    auto &child2 = c.generator("child2");
    parent.add_child_generator("child2", child2);
    auto &clk_child2 = child2.port(PortDirection::In, "clk", 1, PortType::Clock);
    auto &rst_child2 = child2.port(PortDirection::In, "rst", 1, PortType::AsyncReset);
    parent.wire(clk_child2, clk);
    parent.wire(rst_child2, rst);
    {
        auto &a_child = child2.var("a", 1);
        auto &b_child = child2.var("b", 1);
        auto &c_child = child2.var("c", 1);
        auto &flush = child2.port(PortDirection::In, "flush", 1, PortType::Reset);
        parent.wire(flush, constant(1, 1));
        auto seq_child = child2.sequential();
        seq_child->add_condition({EventEdgeType::Posedge, clk_child2.shared_from_this()});
        // same thing as the parent
        auto if_seq_child = std::make_shared<IfStmt>(rst_child2);
        if_seq_child->add_then_stmt(b_child.assign(constant(0, 1)));
        auto if_2 = std::make_shared<IfStmt>(flush);
        if_2->add_then_stmt(c_child.assign(constant(1, 1)));
        if_2->add_else_stmt(c_child.assign(a_child));
        if_seq_child->add_else_stmt(if_2);
        seq_child->add_stmt(if_seq_child);
    }

    // add attribute
    auto attr = std::make_shared<Attribute>();
    attr->value_str = "sync-reset=flush;over_clk_en=false";
    parent.add_attribute(attr);
    auto_insert_sync_reset(&parent);
    fix_assignment_type(&parent);
    create_module_instantiation(&parent);

    auto src = generate_verilog(&parent);
    EXPECT_TRUE(src.find("parent") != src.end());
    EXPECT_TRUE(src.find("child") != src.end());
    EXPECT_TRUE(src.find("child2") != src.end());
    auto src_parent = src.at("parent");
    EXPECT_TRUE(src_parent.find("else if (flush) begin\n"
                                "    b <= 1'h0;\n"
                                "  end") != std::string::npos);
    EXPECT_TRUE(src_parent.find("child2 child2 (\n"
                                "  .clk(clk),\n"
                                "  .flush(flush),") != std::string::npos);
    auto src_child = src.at("child");
    EXPECT_TRUE(src_child.find("else if (flush) begin\n"
                               "    b <= 1'h0;") != std::string::npos);
    auto src_child2 = src.at("child2");
    EXPECT_TRUE(src_child2.find("else if (flush) begin\n"
                                "    c <= 1'h1;") != std::string::npos);
}

TEST(pass, remove_empty_block_always) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");
    mod.sequential();
    remove_empty_block(&mod);
    EXPECT_EQ(mod.stmts_count(), 0);
}

TEST(pass, remove_empty_block_if_then) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");
    auto &out = mod.var("out", 1);
    auto seq = mod.sequential();
    auto if_ = std::make_shared<IfStmt>(out.shared_from_this());
    if_->add_else_stmt(out.assign(constant(1, 1)));
    seq->add_stmt(if_);
    remove_empty_block(&mod);
    EXPECT_EQ(mod.stmts_count(), 1);
    EXPECT_TRUE(if_->else_body()->empty());
    EXPECT_TRUE(!if_->then_body()->empty());
    auto target = if_->predicate();
    EXPECT_EQ(target->to_string(), "~out");
}

TEST(pass, remove_empty_switch_one) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");
    auto &out = mod.var("out", 1);
    auto seq = mod.sequential();
    auto case_ = std::make_shared<SwitchStmt>(out.shared_from_this());
    case_->add_switch_case(constant(0, 1).as<Const>(), out.assign(constant(0, 1)));
    case_->add_switch_case(constant(1, 1).as<Const>(), std::make_shared<ScopedStmtBlock>());
    seq->add_stmt(case_);
    remove_empty_block(&mod);
    EXPECT_EQ(case_->body().size(), 1);
}

TEST(pass, remove_empty_switch_all) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");
    auto &out = mod.var("out", 1);
    auto seq = mod.sequential();
    auto case_ = std::make_shared<SwitchStmt>(out.shared_from_this());
    seq->add_stmt(case_);
    remove_empty_block(&mod);
    EXPECT_EQ(mod.stmts_count(), 0);
}

TEST(pass, unused_var) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");
    auto &port1 = mod.port(PortDirection::In, "in", 1);
    auto &port2 = mod.port(PortDirection::Out, "out", 1);
    auto &var1 = mod.var("c", 1);
    auto &var2 = mod.var("d", 1);
    mod.add_stmt(var1.assign(port1));
    mod.add_stmt(port2.assign(var1));
    // var2 is unused
    (void)var2;

    EXPECT_TRUE(mod.get_var("d") != nullptr);
    remove_unused_vars(&mod);

    EXPECT_TRUE(mod.get_var("d") == nullptr);
    EXPECT_TRUE(mod.get_var("in") != nullptr);
    EXPECT_TRUE(mod.get_var("c") != nullptr);
}

TEST(pass, dead_code_elimination_1) {
    Context c;
    auto &mod = c.generator("mod");
    auto &a = mod.var("a", 1);
    auto &b = mod.var("b", 1);
    mod.wire(a, b);

    dead_code_elimination(&mod);
    EXPECT_TRUE(mod.get_vars().empty());
}

TEST(pass, dead_code_elimination_2) {
    // remove statements inside scopes
    Context ctx;
    auto &mod = ctx.generator("mod");
    auto &a = mod.var("a", 1);
    auto &b = mod.var("b", 1);
    auto &c = mod.var("c", 1);
    mod.wire(a, b);
    auto const &comb = mod.combinational();
    comb->add_stmt(c.assign(a));

    dead_code_elimination(&mod);
    EXPECT_TRUE(mod.get_vars().empty());
    EXPECT_TRUE(mod.get_all_stmts().empty());
}

TEST(pass, dead_code_elimination_3) {
    // cross boundary of modules
    Context ctx;
    auto &mod = ctx.generator("mod");
    auto &child = ctx.generator("child");
    mod.add_child_generator("inst", child);
    auto &in1 = child.port(PortDirection::In, "in1", 1);
    auto &in2 = child.port(PortDirection::In, "in2", 1);
    auto &v = child.var("v", 1);
    child.wire(v, in1 & in2);
    auto &v1 = mod.var("v1", 1);
    auto &v2 = mod.var("v2", 1);
    mod.wire(in1, v1);
    mod.wire(in2, v2);

    fix_assignment_type(&mod);
    verify_generator_connectivity(&mod);
    verify_assignments(&mod);

    dead_code_elimination(&mod);
    EXPECT_TRUE(mod.get_vars().empty());
    EXPECT_EQ(mod.get_child_generator_size(), 0);
}
