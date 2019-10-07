#include "../src/codegen.hh"
#include "../src/except.hh"
#include "../src/expr.hh"
#include "../src/fsm.hh"
#include "../src/generator.hh"
#include "../src/pass.hh"
#include "../src/port.hh"
#include "../src/stmt.hh"
#include "../src/util.hh"
#include "gtest/gtest.h"

using namespace kratos;

TEST(generator, load) {  // NOLINT
    Context c;
    auto mod = Generator::from_verilog(&c, "module1.sv", "module1", {}, {});
    EXPECT_TRUE(mod.get_port("f") != nullptr);
    mod = Generator::from_verilog(&c, "module1.sv", "module2", {}, {});
    EXPECT_TRUE(mod.get_port("f") != nullptr);
    ASSERT_ANY_THROW(Generator::from_verilog(&c, "module1.sv", "module3", {}, {}));
    ASSERT_ANY_THROW(Generator::from_verilog(&c, "module1.sv", "module1", {"NON_EXIST"}, {}));
    mod = Generator::from_verilog(&c, "module1.sv", "module1", {}, {{"a", PortType::Clock}});
    EXPECT_EQ(mod.get_port("a")->port_type(), PortType::Clock);
    ASSERT_ANY_THROW(
        Generator::from_verilog(&c, "module1.sv", "module1", {}, {{"aa", PortType::Clock}}));
}

TEST(generator, port) {  // NOLINT
    Context c;
    auto mod = c.generator("module");
    mod.port(PortDirection::In, "in", 1);
    mod.port(PortDirection::Out, "out", 1);
}

TEST(generator, rename_var) {  // NOLINT
    Context c;
    auto mod = c.generator("module");
    auto &a = mod.var("a", 2);
    auto &b = mod.var("b", 2);
    auto &d = mod.var("d", 1);
    auto stmt1 = a.assign(b);
    auto stmt2 = d.assign(a[std::make_pair(0, 0)]);
    mod.rename_var("a", "c");
    EXPECT_EQ(a.name, "c");
    EXPECT_EQ(stmt1->left()->to_string(), "c");
    EXPECT_EQ(stmt2->right()->to_string(), "c[0]");
}

TEST(generator, remove_stmt) {  // NOLINT
    Context c;
    auto mod = c.generator("module");
    auto &a = mod.var("a", 2);
    auto &b = mod.var("b", 2);
    auto stmt = a.assign(b);
    mod.add_stmt(stmt);
    EXPECT_EQ(mod.get_stmt(0), stmt);
    mod.remove_stmt(stmt);
    EXPECT_EQ(mod.get_stmt(0), nullptr);
}

TEST(generator, param) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");
    auto &out = mod.port(PortDirection::Out, "out", 1);
    auto &child = c.generator("child");
    auto &child_out = child.port(PortDirection::Out, "out", 1);
    auto &param = child.parameter("parm", 1);
    param.set_value(1);
    child.add_stmt(child_out.assign(param));
    mod.add_child_generator("inst", child.shared_from_this());
    mod.add_stmt(out.assign(child_out));

    fix_assignment_type(&mod);
    create_module_instantiation(&mod);
    auto mod_src = generate_verilog(&mod);
    EXPECT_TRUE(is_valid_verilog(mod_src));
}

TEST(pass, assignment_fix) {  // NOLINT
    Context c;
    auto mod = c.generator("module");
    auto &port1 = mod.port(PortDirection::In, "in", 1);
    auto &port2 = mod.port(PortDirection::Out, "out", 1);

    auto expr = port2.assign(port1);
    mod.add_stmt(expr);
    fix_assignment_type(&mod);
    EXPECT_EQ(expr->assign_type(), AssignmentType::Blocking);
}

TEST(pass, unused_var) {  // NOLINT
    Context c;
    auto mod = c.generator("module");
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

TEST(pass, verilog_code_gen) {  // NOLINT
    Context c;
    auto &mod1 = c.generator("module1");
    auto &port1 = mod1.port(PortDirection::In, "in", 1);
    auto &port2 = mod1.port(PortDirection::Out, "out", 1);
    mod1.add_stmt(port2.assign(port1, AssignmentType::Blocking));
    auto const &result = generate_verilog(&mod1);
    EXPECT_EQ(result.size(), 1);
    EXPECT_TRUE(result.find("module1") != result.end());
    auto module_str = result.at("module1");
    EXPECT_FALSE(module_str.empty());
}

TEST(pass, generator_hash) {  // NOLINT
    Context c;
    auto &mod1 = c.generator("module1");
    auto &port1_1 = mod1.port(PortDirection::In, "in", 1);
    auto &port1_2 = mod1.port(PortDirection::Out, "out", 1);
    mod1.add_stmt(port1_2.assign(port1_1, AssignmentType::Blocking));

    auto &mod2 = c.generator("module1");
    auto &port2_1 = mod2.port(PortDirection::In, "in", 1);
    auto &port2_2 = mod2.port(PortDirection::Out, "out", 1);
    mod2.add_stmt(port2_2.assign(port2_1, AssignmentType::Blocking));

    auto &mod3 = c.generator("module1");
    auto &port3_1 = mod3.port(PortDirection::In, "in", 1);
    auto &port3_2 = mod3.port(PortDirection::Out, "out", 1);
    mod3.add_stmt(port3_2.assign(port3_1 + constant(1, 1), AssignmentType::Blocking));

    hash_generators(&mod1, HashStrategy::SequentialHash);
    auto mod1_hash = c.get_hash(&mod1);
    hash_generators(&mod2, HashStrategy::SequentialHash);
    auto mod2_hash = c.get_hash(&mod2);
    hash_generators(&mod3, HashStrategy::ParallelHash);
    auto mod3_hash = c.get_hash(&mod3);

    EXPECT_EQ(mod1_hash, mod2_hash);
    EXPECT_NE(mod1_hash, mod3_hash);

    // use mod1 as top. this is fine since we manually force other modules to be hashed
    mod1.add_child_generator("inst0", mod2.shared_from_this());
    mod1.add_child_generator("inst1", mod3.shared_from_this());

    // this should be the same as mod2
    auto &mod4 = c.generator("module1");
    auto &port4_1 = mod4.port(PortDirection::In, "in", 1);
    auto &port4_2 = mod4.port(PortDirection::Out, "out", 1);
    mod4.add_stmt(port4_2.assign(port4_1, AssignmentType::Blocking));
    mod1.add_child_generator("inst4", mod4.shared_from_this());

    hash_generators(&mod1, HashStrategy::SequentialHash);
    uniquify_generators(&mod1);
    EXPECT_EQ(mod1.name, "module1");
    EXPECT_EQ(mod2.name, "module1_unq0");
    EXPECT_EQ(mod3.name, "module1_unq1");
    EXPECT_EQ(mod4.name, mod2.name);
}

TEST(pass, decouple1) {  // NOLINT
    Context c;
    auto &mod1 = c.generator("module1");
    auto &port1_1 = mod1.port(PortDirection::In, "in", 1);
    auto &port1_2 = mod1.port(PortDirection::Out, "out", 1);

    auto &mod2 = c.generator("module2");
    auto &port2_1 = mod2.port(PortDirection::In, "in", 1);
    // auto &port2_2 = mod2.port(PortDirection::Out, "out", 1);

    auto &mod3 = c.generator("module3");
    auto &port3_1 = mod3.port(PortDirection::In, "in", 2);
    // auto &port3_2 = mod3.port(PortDirection::Out, "out", 1);

    mod1.add_child_generator("inst0", mod2.shared_from_this());
    mod1.add_child_generator("inst1", mod3.shared_from_this());

    mod1.add_stmt(port2_1.assign(port1_2));
    mod1.add_stmt(port3_1.assign(port1_1.concat(port2_1)));

    EXPECT_EQ(mod1.stmts_count(), 2);
    decouple_generator_ports(&mod1);
    check_mixed_assignment(&mod1);
    EXPECT_EQ(mod1.stmts_count(), 2);
    auto new_var = mod1.get_var("inst1_in");
    EXPECT_TRUE(new_var != nullptr);

    EXPECT_EQ(new_var->sources().size(), 1);
    auto new_var_src = (*new_var->sources().begin())->right();
    EXPECT_EQ(new_var_src, port1_1.concat(port2_1).shared_from_this());
}

TEST(pass, verilog_instance) {  // NOLINT
    Context c;
    auto &mod1 = c.generator("module1");
    mod1.debug = true;
    auto &port1_1 = mod1.port(PortDirection::In, "in", 1);
    auto &port1_2 = mod1.port(PortDirection::Out, "out", 1);

    auto &mod2 = c.generator("module2");
    auto &port2_1 = mod2.port(PortDirection::In, "in", 2);
    auto &port2_2 = mod2.port(PortDirection::Out, "out", 2);

    auto stmt = port2_2.assign(port2_1);
    mod2.add_stmt(stmt);
    stmt = port2_1.assign(port1_1.concat(port1_1));
    mod1.add_stmt(stmt);
    stmt = port1_2.assign(port2_2[0]);
    mod1.add_stmt(stmt);

    mod1.add_child_generator("inst0", mod2.shared_from_this());
    // lazy. just use this pass to fix the assignment type
    decouple_generator_ports(&mod1);
    fix_assignment_type(&mod1);
    create_module_instantiation(&mod1);
    auto const &result = generate_verilog(&mod1);
    EXPECT_EQ(result.size(), 2);
    EXPECT_TRUE(result.find("module1") != result.end());
    EXPECT_TRUE(is_valid_verilog(result));
}

TEST(pass, verilog_stub) {  // NOLINT
    Context c;
    auto &mod1 = c.generator("module1");
    mod1.port(PortDirection::In, "in", 1);
    mod1.port(PortDirection::Out, "out", 1);
    // set it to stub
    mod1.set_is_stub(true);

    EXPECT_NO_THROW(zero_out_stubs(&mod1));

    EXPECT_NO_THROW(verify_generator_connectivity(&mod1));
}

TEST(pass, if_case) {  // NOLINT
    Context c;
    auto &mod = c.generator("module1");
    auto &in = mod.port(PortDirection::In, "in", 3);
    auto &out = mod.port(PortDirection::Out, "out", 3);
    auto if_stmt = std::make_shared<IfStmt>(in.eq(constant(0, 3)));
    if_stmt->add_then_stmt(out.assign(constant(0, 3)));
    auto if_stmt2 = std::make_shared<IfStmt>(in.eq(constant(1, 3)));
    if_stmt2->add_then_stmt(out.assign(constant(1, 3)));
    if_stmt->add_else_stmt(if_stmt2);
    auto stmt_list = std::make_shared<CombinationalStmtBlock>();
    stmt_list->add_stmt(if_stmt);
    mod.add_stmt(stmt_list);

    transform_if_to_case(&mod);
    auto stmt = reinterpret_cast<Stmt *>(mod.get_child(0)->get_child(0));
    EXPECT_TRUE(stmt->type() == StatementType::Switch);
    auto switch_ = stmt->as<SwitchStmt>();
    EXPECT_EQ(switch_->body().size(), 2);

    fix_assignment_type(&mod);
    auto result = generate_verilog(&mod);
    EXPECT_TRUE(result.find("module1") != result.end());
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

TEST(pass, replace) {  // NOLINT
    Context c;
    auto &mod1 = c.generator("module1");
    auto &in1 = mod1.port(PortDirection::In, "in", 1);
    auto &out1 = mod1.port(PortDirection::Out, "out", 1);

    auto &mod2 = c.generator("module2");
    auto &in2 = mod2.port(PortDirection::In, "in", 1);
    auto &out2 = mod2.port(PortDirection::Out, "out", 1);
    mod2.add_stmt(out2.assign(in2));

    auto &mod3 = c.generator("module3");
    auto &in3 = mod3.port(PortDirection::In, "in", 2);
    auto &out3 = mod3.port(PortDirection::Out, "out", 2);
    mod3.add_stmt(out3.assign(in3));

    mod1.add_child_generator("inst0", mod2.shared_from_this());
    mod1.add_stmt(in2.assign(in1));
    mod1.add_stmt(out1.assign(out2));

    EXPECT_THROW(mod1.replace(mod2.instance_name, mod3.shared_from_this()), VarException);
    in3.var_width() = 1;
    out3.var_width() = 1;
    EXPECT_NO_THROW(mod1.replace(mod2.instance_name, mod3.shared_from_this()));
    EXPECT_EQ(mod1.get_child_generator_size(), 1);
    fix_assignment_type(&mod1);
    create_module_instantiation(&mod1);
    auto mod_src = generate_verilog(&mod1);
    auto src = mod_src["module1"];
    EXPECT_TRUE(src.find("module2") == std::string::npos);
    EXPECT_TRUE(src.find("module3") != std::string::npos);
}

TEST(pass, decouple_generator_ports) {  // NOLINT
    Context c;
    auto &mod1 = c.generator("module1");
    auto &in1 = mod1.port(PortDirection::In, "in", 1);
    auto &out1 = mod1.port(PortDirection::Out, "out", 1);

    auto &mod2 = c.generator("module2");
    auto &in2 = mod2.port(PortDirection::In, "in", 1);
    auto &out2 = mod2.port(PortDirection::Out, "out", 1);
    mod2.add_stmt(out2.assign(in2, AssignmentType::Blocking));

    auto &mod3 = c.generator("module3");
    auto &in3 = mod3.port(PortDirection::In, "in", 1);
    auto &out3 = mod3.port(PortDirection::Out, "out", 1);
    mod3.add_stmt(out3.assign(in3, AssignmentType::Blocking));

    mod1.add_child_generator("inst0", mod2.shared_from_this());
    mod1.add_child_generator("inst1", mod3.shared_from_this());

    mod1.add_stmt(in2.assign(in1));
    mod1.add_stmt(in3.assign(in1));

    mod1.add_stmt(out1.assign(out2 + out3));

    VerilogModule verilog(&mod1);
    PassManager &manager = verilog.pass_manager();
    manager.add_pass("fix_assignment_type");
    manager.add_pass("decouple_generator_ports");
    manager.add_pass("check_mixed_assignment");
    manager.add_pass("create_module_instantiation");
    manager.add_pass("hash_generators_parallel");
    verilog.run_passes();
    auto src = verilog.verilog_src();
    EXPECT_EQ(src.size(), 3);
}

TEST(pass, module_hash) {  // NOLINT
    Context c;
    auto &mod1 = c.generator("module1");
    auto &in1 = mod1.port(PortDirection::In, "in", 1);
    auto &out1 = mod1.port(PortDirection::Out, "out", 1);

    auto &mod2 = c.generator("module2");
    auto &in2 = mod2.port(PortDirection::In, "in", 1);
    auto &out2 = mod2.port(PortDirection::Out, "out", 1);
    mod2.add_stmt(out2.assign(in2, AssignmentType::Blocking));

    auto &mod3 = c.generator("module1");
    mod1.add_child_generator("inst0", mod3.shared_from_this());

    mod1.add_child_generator("inst1", mod2.shared_from_this());
    mod1.add_stmt(in2.assign(in1));
    mod1.add_stmt(out1.assign(out2));

    fix_assignment_type(&mod1);
    create_module_instantiation(&mod1);

    hash_generators(&mod1, HashStrategy::SequentialHash);
    hash_generators(&mod1, HashStrategy::ParallelHash);
}

TEST(pass, zero_input_port1) {  // NOLINT
    Context c;
    auto &mod1 = c.generator("module1");
    auto &in1 = mod1.port(PortDirection::In, "in", 2);
    auto &out1 = mod1.port(PortDirection::Out, "out", 2);
    mod1.add_stmt(out1.assign(in1.shared_from_this()));

    // the parent
    auto mod2 = c.generator("module2");
    auto &in2 = mod2.port(PortDirection::In, "in", 1);
    auto &out2 = mod2.port(PortDirection::Out, "out", 2);
    mod2.add_child_generator("mod", mod1.shared_from_this());
    mod2.add_stmt(in1[0].assign(in2));
    mod2.add_stmt(out2.assign(out1));

    // add attribute
    auto attr = std::make_shared<Attribute>();
    attr->type_str = "zero_inputs";
    mod2.add_attribute(attr);

    // this one won't pass
    EXPECT_THROW(verify_generator_connectivity(&mod2), StmtException);
    // now fix the connections
    zero_generator_inputs(&mod2);
    EXPECT_NO_THROW(verify_generator_connectivity(&mod2));
}

TEST(pass, zero_input_port2) {  // NOLINT
    // TODO: change this into a parametrized test
    Context c;
    auto &mod1 = c.generator("module1");
    auto &in1 = mod1.port(PortDirection::In, "in", 2, 2);
    auto &out1 = mod1.port(PortDirection::Out, "out", 2, 2);
    mod1.add_stmt(out1.assign(in1.shared_from_this()));

    // the parent
    auto mod2 = c.generator("module2");
    auto &in2 = mod2.port(PortDirection::In, "in", 1, 2);
    auto &out2 = mod2.port(PortDirection::Out, "out", 2, 2);
    mod2.add_child_generator("mod", mod1.shared_from_this());
    mod2.add_stmt(in1[0].assign(in2));
    mod2.add_stmt(out2.assign(out1));

    // add attribute
    auto attr = std::make_shared<Attribute>();
    attr->type_str = "zero_inputs";
    mod2.add_attribute(attr);

    // this one won't pass
    EXPECT_THROW(verify_generator_connectivity(&mod2), StmtException);
    // now fix the connections
    zero_generator_inputs(&mod2);
    EXPECT_NO_THROW(verify_generator_connectivity(&mod2));
}

TEST(generator, replace) {  // NOLINT
    Context c;
    auto &mod1 = c.generator("module1");
    auto &in1 = mod1.port(PortDirection::In, "in", 1);
    auto &out1 = mod1.port(PortDirection::Out, "out", 1);

    auto &mod2 = c.generator("module2");
    auto &in2 = mod2.port(PortDirection::In, "in", 1);
    auto &out2 = mod2.port(PortDirection::Out, "out", 1);
    mod2.add_stmt(out2.assign(in2));

    auto &mod3 = c.generator("module3");
    auto &in3 = mod3.port(PortDirection::In, "in", 1);
    auto &out3 = mod3.port(PortDirection::Out, "out", 1);
    mod3.add_stmt(out3.assign(in3));

    mod1.add_child_generator("mod", mod2.shared_from_this());
    mod1.add_stmt(in2.assign(in1));
    mod1.add_stmt(out1.assign(out2));

    EXPECT_NO_THROW(verify_generator_connectivity(&mod1));
    mod1.replace("mod", mod3.shared_from_this());
    EXPECT_NO_THROW(verify_generator_connectivity(&mod1));
}

TEST(generator, bundle_to_struct) {  // NOLINT
    Context c;
    auto def = std::make_shared<PortBundleDefinition>("bundle");
    def->add_definition("a", 1, 1, false, PortDirection::In, PortType::Data);
    def->add_definition("b", 1, 1, false, PortDirection::In, PortType::Data);
    auto &mod1 = c.generator("module1");
    auto &mod2 = c.generator("module2");
    auto &mod3 = c.generator("module3");

    // mod2 definition
    mod2.add_bundle_port_def("p", def);
    auto &port2_a = mod2.port(PortDirection::Out, "a", 1);
    auto &port2_b = mod2.port(PortDirection::Out, "b", 1);
    mod2.add_stmt(port2_a.assign(mod2.get_bundle_ref("p")->get_port("a")));
    mod2.add_stmt(port2_b.assign(mod2.get_bundle_ref("p")->get_port("b")));
    mod1.add_child_generator("mod2", mod2.shared_from_this());

    // mod3 definition
    mod3.add_bundle_port_def("p", def->flip());
    auto &port3_a = mod3.port(PortDirection::In, "a", 1);
    auto &port3_b = mod3.port(PortDirection::In, "b", 1);
    mod3.add_stmt(mod3.get_bundle_ref("p")->get_port("a").assign(port3_a));
    mod3.add_stmt(mod3.get_bundle_ref("p")->get_port("b").assign(port3_b));
    mod1.add_child_generator("mod3", mod3.shared_from_this());

    // mod1 definition
    auto &mod1_a = mod1.port(PortDirection::In, "a", 1);
    auto &mod1_b = mod1.port(PortDirection::Out, "b", 1);
    mod1.add_stmt(mod2.get_bundle_ref("p")->get_port("a").assign(mod1_a));
    mod1.add_stmt(mod2.get_bundle_ref("p")->get_port("b").assign(mod1_a));
    mod1.add_stmt(port3_a.assign(mod1_a));
    mod1.add_stmt(port3_b.assign(mod1_a));
    mod1.add_stmt(mod1_b.assign(mod3.get_bundle_ref("p")->get_port("b") + port2_b));

    // run bundle to pack pass
    fix_assignment_type(&mod1);
    verify_generator_connectivity(&mod1);
    // remove_pass_through_modules(&mod1);
    change_port_bundle_struct(&mod1);
    verify_generator_connectivity(&mod1);
    decouple_generator_ports(&mod1);
    create_module_instantiation(&mod1);
    remove_fanout_one_wires(&mod1);
    generate_verilog(&mod1);
}

TEST(generator, fsm) {  // NOLINT
    Context c;
    auto mod = c.generator("mod");
    auto &out_ = mod.port(PortDirection::Out, "out", 2);
    auto &in_ = mod.port(PortDirection::In, "in", 2);
    mod.port(PortDirection::In, "clk", 1, 1, PortType::Clock, false);
    mod.port(PortDirection::In, "rst", 1, 1, PortType::AsyncReset, false);

    auto &fsm = mod.fsm("Color");
    fsm.output(out_.shared_from_this());

    auto red = fsm.add_state("Red");
    auto blue = fsm.add_state("Blue");
    auto expr1 = in_.eq(constant(0, 2)).shared_from_this();
    red->next(red, expr1);
    auto expr2 = in_.eq(constant(1, 2)).shared_from_this();
    red->next(blue, expr2);
    blue->next(red, expr2);

    red->output(out_.shared_from_this(), constant(2, 2).shared_from_this());
    blue->output(out_.shared_from_this(), constant(1, 2).shared_from_this());
    fsm.set_start_state(red);

    realize_fsm(&mod);
    fix_assignment_type(&mod);
    verify_generator_connectivity(&mod);
    auto mod_src = generate_verilog(&mod);
    is_valid_verilog(mod_src);
}

TEST(generator, function_call_stmt) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");
    mod.fn_name_ln.emplace_back("", 1);
    auto &in_ = mod.port(PortDirection::In, "in", 2);
    auto &out_ = mod.port(PortDirection::Out, "out", 2);
    auto func = mod.function("test");
    auto func_in = func->input("in_arg", 2, false);
    func->add_stmt(out_.assign(func_in, AssignmentType::Blocking));
    std::map<std::string, std::shared_ptr<Var>> args = {{"in_arg", in_.shared_from_this()}};
    auto stmt = std::make_shared<FunctionCallStmt>(func, args);
    auto comb = mod.combinational();
    comb->add_stmt(stmt);

    verify_generator_connectivity(&mod);
    extract_debug_info(&mod);
    auto mod_src = generate_verilog(&mod);
    is_valid_verilog(mod_src);
}

TEST(generator, function_return) {  // NOLINT
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

TEST(generator, var_var_slicing) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");
    auto &a = mod.var("a", 16, 4);
    auto &in = mod.port(PortDirection::In, "in", 2);
    auto &out = mod.port(PortDirection::Out, "out", 16);
    mod.add_stmt(out.assign(a[in.shared_from_this()], AssignmentType::Blocking));

    check_mixed_assignment(&mod);
    verify_generator_connectivity(&mod);
}

TEST(generator, var_concat_check) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");
    auto &in = mod.port(PortDirection::In, "in", 1);
    auto &out = mod.port(PortDirection::Out, "out", 2);
    mod.add_stmt(out.assign(constant(0, 1).concat(in), Blocking));

    EXPECT_NO_THROW(check_mixed_assignment(&mod));
}

TEST(generator, mixed_assignment) {  // NOLINT
    Context c;
    auto &mod1 = c.generator("mod1");
    auto &in1 = mod1.port(PortDirection::In, "in", 1);
    auto &out2 = mod1.port(PortDirection::Out, "out", 1);

    auto &mod2 = c.generator("mod2");
    auto &var = mod2.var("a", 1);
    mod1.add_child_generator("test", mod2.shared_from_this());

    mod1.add_stmt(out2.assign(in1 + var, Blocking));

    EXPECT_THROW(check_mixed_assignment(&mod1), VarException);
}

TEST(generator, active_low) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");
    auto &rst = mod.port(PortDirection::In, "reset", 1, 1, PortType::AsyncReset, false);
    auto seq = mod.sequential();
    rst.set_active_high(true);
    seq->add_condition({BlockEdgeType::Negedge, rst.shared_from_this()});
    EXPECT_THROW(check_active_high(&mod), VarException);
}

TEST(generator, nested_fsm) {  // NOLINT
    Context c;
    auto mod = c.generator("mod");
    auto &out_ = mod.port(PortDirection::Out, "out", 2);
    auto &in_ = mod.port(PortDirection::In, "in", 2);
    mod.port(PortDirection::In, "clk", 1, 1, PortType::Clock, false);
    mod.port(PortDirection::In, "rst", 1, 1, PortType::AsyncReset, false);

    auto &fsm = mod.fsm("Color");
    fsm.output(out_.shared_from_this());

    auto red = fsm.add_state("Red");
    auto blue = fsm.add_state("Blue");
    auto expr1 = in_.eq(constant(0, 2)).shared_from_this();
    red->next(red, expr1);
    auto expr2 = in_.eq(constant(1, 2)).shared_from_this();
    red->next(blue, expr2);
    blue->next(red, expr2);

    red->output(out_.shared_from_this(), constant(2, 2).shared_from_this());
    blue->output(out_.shared_from_this(), constant(1, 2).shared_from_this());
    fsm.set_start_state(red);

    auto &second_state = mod.fsm("Idle");
    fsm.add_child_fsm(&second_state);
    second_state.output(out_.shared_from_this());
    auto idle = second_state.add_state("idle");
    idle->output(out_.shared_from_this(), nullptr);
    idle->next(idle, nullptr);
    auto expr3 = in_.eq(constant(2, 2)).shared_from_this();
    red->next(idle, expr3);

    auto states = fsm.get_all_child_states(false);
    EXPECT_EQ(states.size(), 3);
    realize_fsm(&mod);
    fix_assignment_type(&mod);
    generate_verilog(&mod);
}

TEST(generator, slide_through_fsm) {  // NOLINT
    Context c;
    auto mod = c.generator("mod");
    auto &out_ = mod.port(PortDirection::Out, "out", 2);
    mod.port(PortDirection::In, "clk", 1, 1, PortType::Clock, false);
    mod.port(PortDirection::In, "rst", 1, 1, PortType::AsyncReset, false);

    auto &fsm = mod.fsm("Color");
    fsm.output(out_.shared_from_this());

    auto red = fsm.add_state("Red");
    auto blue = fsm.add_state("Blue");
    fsm.set_start_state(red);
    red->next(blue, nullptr);
    blue->next(red, nullptr);
    auto &output_value = constant(1, 2);
    red->output(out_.shared_from_this(), output_value.shared_from_this());
    blue->output(out_.shared_from_this(), output_value.shared_from_this());

    realize_fsm(&mod);
    fix_assignment_type(&mod);
    generate_verilog(&mod);
}

TEST(generator, non_synthesizable) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");
    auto comb = mod.combinational();
    auto dpi = mod.dpi_function("test_dpi");
    auto &call = mod.call("test_dpi", {});
    auto stmt = std::make_shared<FunctionCallStmt>(call.as<FunctionCallVar>());
    comb->add_stmt(stmt);
    // add debug info
    stmt->fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));

    // run the pass
    EXPECT_THROW(check_non_synthesizable_content(&mod), UserException);
}

TEST(generator, latch) {  // NOLINT
    Context c;
    auto &mod = c.generator("module");
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

TEST(generator, latch_rst) {  // NOLINT
    Context c;
    auto &mod = c.generator("module");
    auto &in = mod.port(PortDirection::In, "in", 1);
    auto &out = mod.port(PortDirection::Out, "out", 1);
    auto &clk = mod.port(PortDirection::In, "clk", 1, 1, PortType::Clock, false);
    auto &rst = mod.port(PortDirection::In, "rst", 1, 1, PortType::AsyncReset, false);
    auto &cen = mod.port(PortDirection::In, "cen", 1, 1, PortType::ClockEnable, false);

    auto seq = mod.sequential();
    seq->add_condition({BlockEdgeType::Posedge, clk.shared_from_this()});
    seq->add_condition({BlockEdgeType::Posedge, rst.shared_from_this()});
    auto if_ = std::make_shared<IfStmt>(rst);
    if_->add_then_stmt(out.assign(constant(0, 1)));
    auto if__ = std::make_shared<IfStmt>(cen);
    if__->add_then_stmt(out.assign(in));
    if_->add_else_stmt(if__);
    seq->add_stmt(if_);

    EXPECT_NO_THROW(check_inferred_latch(&mod));
}

TEST(generator, decouple2) {  // NOLINT
    Context c;
    auto &mod1 = c.generator("parent");
    auto &port1_1 = mod1.port(PortDirection::In, "in", 1);
    auto &port1_2 = mod1.port(PortDirection::Out, "out", 1);

    auto &mod2 = c.generator("child");
    auto &port2_1 = mod2.port(PortDirection::In, "in", 1);
    auto &port2_2 = mod2.port(PortDirection::Out, "out", 1);
    mod2.add_stmt(port2_2.assign(port2_1));

    auto &mod3 = c.generator("child");
    auto &port3_1 = mod3.port(PortDirection::In, "in", 1);
    auto &port3_2 = mod3.port(PortDirection::Out, "out", 1);
    mod3.add_stmt(port3_2.assign(port3_1));

    auto &mod4 = c.generator("child");
    auto &port4_1 = mod4.port(PortDirection::In, "in", 1);
    auto &port4_2 = mod4.port(PortDirection::Out, "out", 1);
    mod4.add_stmt(port4_2.assign(port4_1));

    auto inputs = {port2_1.shared_from_this(), port3_1.shared_from_this(),
                   port4_1.shared_from_this()};
    auto mods = {&mod2, &mod3, &mod4};
    auto count = 0;
    for (auto mod: mods) {
        mod1.add_child_generator("mod" + std::to_string(count++), mod->shared_from_this());
    }
    for (auto const &in: inputs) {
        mod1.add_stmt(in->assign(port1_1));
    }
    mod1.add_stmt(port1_2.assign(port2_2 ^ port3_2 ^ port4_2));
    fix_assignment_type(&mod1);
    decouple_generator_ports(&mod1);
    hash_generators_sequential(&mod1);
    auto result = generate_verilog(&mod1);
    auto mod_src = result.at("parent");
    EXPECT_TRUE(mod_src.find("mod0_out ^ mod1_out ^ mod2_out") != std::string::npos);
}