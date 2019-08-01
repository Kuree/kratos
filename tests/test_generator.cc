#include "../src/codegen.hh"
#include "../src/expr.hh"
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
    auto stmt2 = d.assign(a[{0, 0}]);
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

    EXPECT_ANY_THROW(verify_generator_connectivity(&mod1));
    mod1.add_stmt(port2.assign(port1));

    EXPECT_NO_THROW(verify_generator_connectivity(&mod1));

    auto &mod2 = c.generator("module2");
    EXPECT_NE(&mod1, &mod2);

    mod1.add_child_generator("inst", mod2.shared_from_this());
    EXPECT_ANY_THROW(mod1.port(PortDirection::In, "in", 1));
    auto &port3 = mod2.port(PortDirection::In, "in", 1);
    mod1.add_stmt(port3.assign(port1));
    EXPECT_NO_THROW(verify_generator_connectivity(&mod1));

    auto &port4 = mod2.port(PortDirection::Out, "out", 1);
    EXPECT_ANY_THROW(verify_generator_connectivity(&mod1));
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
    mod3.add_stmt(
        port3_2.assign(port3_1 + mod3.constant(1, 1), AssignmentType::Blocking));

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
    auto if_stmt = std::make_shared<IfStmt>(in.eq(mod.constant(0, 3)));
    if_stmt->add_then_stmt(out.assign(mod.constant(0, 3)));
    auto if_stmt2 = std::make_shared<IfStmt>(in.eq(mod.constant(1, 3)));
    if_stmt2->add_then_stmt(out.assign(mod.constant(1, 3)));
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

    EXPECT_ANY_THROW(
        mod1.replace_child_generator(mod2.shared_from_this(), mod3.shared_from_this()));
    in3.width = 1;
    out3.width = 1;
    EXPECT_NO_THROW(mod1.replace_child_generator(mod2.shared_from_this(), mod3.shared_from_this()));
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
    manager.add_pass("create_module_instantiation");
    manager.add_pass("hash_generators_parallel");
    verilog.run_passes();
    auto src = verilog.verilog_src();
    EXPECT_EQ(src.size(), 3);
    EXPECT_TRUE(is_valid_verilog(src));
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

TEST(pass, zero_input_port1) {   // NOLINT
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
    EXPECT_ANY_THROW(verify_generator_connectivity(&mod2));
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
    EXPECT_ANY_THROW(verify_generator_connectivity(&mod2));
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

TEST(generator, bundle_to_struct) { // NOLINT
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
    //remove_pass_through_modules(&mod1);
    change_port_bundle_struct(&mod1);
    verify_generator_connectivity(&mod1);
    decouple_generator_ports(&mod1);
    create_module_instantiation(&mod1);
    remove_fanout_one_wires(&mod1);
    generate_verilog(&mod1);
}