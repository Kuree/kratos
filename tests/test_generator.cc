#include "../src/codegen.hh"
#include "../src/debug.hh"
#include "../src/except.hh"
#include "../src/expr.hh"
#include "../src/formal.hh"
#include "../src/fsm.hh"
#include "../src/generator.hh"
#include "../src/interface.hh"
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
    auto &mod = c.generator("mod");
    mod.port(PortDirection::In, "in", 1);
    mod.port(PortDirection::Out, "out", 1);
}

TEST(generator, rename_var) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");
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
    auto &mod = c.generator("mod");
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
    // EXPECT_TRUE(is_valid_verilog(mod_src));
}

TEST(pass, assignment_fix) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");
    auto &port1 = mod.port(PortDirection::In, "in", 1);
    auto &port2 = mod.port(PortDirection::Out, "out", 1);

    auto expr = port2.assign(port1);
    mod.add_stmt(expr);
    fix_assignment_type(&mod);
    EXPECT_EQ(expr->assign_type(), AssignmentType::Blocking);
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
    auto &port1_3 = mod1.port(PortDirection::Out, "out2", 2);

    auto &mod2 = c.generator("module2");
    auto &port2_1 = mod2.port(PortDirection::In, "in", 1);
    auto &port2_2 = mod2.port(PortDirection::Out, "out", 1);

    auto &mod3 = c.generator("module3");
    auto &port3_1 = mod3.port(PortDirection::In, "in", 2);
    auto &port3_2 = mod3.port(PortDirection::Out, "out", 1);

    mod1.add_child_generator("inst0", mod2.shared_from_this());
    mod1.add_child_generator("inst1", mod3.shared_from_this());

    mod1.add_stmt(port2_1.assign(port1_2));
    mod1.add_stmt(port3_1.assign(port1_1.concat(port2_1)));
    auto stmt = port1_3.assign(port2_2.concat(port3_2));
    mod1.add_stmt(stmt);

    EXPECT_EQ(mod1.stmts_count(), 3);
    decouple_generator_ports(&mod1);
    create_module_instantiation(&mod1);
    check_mixed_assignment(&mod1);
    EXPECT_EQ(mod1.stmts_count(), 2 + 2);
    auto new_var = mod1.get_var("inst1_in");
    EXPECT_TRUE(new_var != nullptr);

    EXPECT_EQ(new_var->sources().size(), 1);
    auto new_var_src = (*new_var->sources().begin())->right();
    EXPECT_EQ(new_var_src, &port1_1.concat(port2_1));
    EXPECT_EQ(stmt->right()->to_string(), "{inst0_out, inst1_out}");
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
    if_stmt2->add_else_stmt(out.assign(constant(0, 3)));
    if_stmt->add_else_stmt(if_stmt2);
    auto stmt_list = std::make_shared<CombinationalStmtBlock>();
    stmt_list->add_stmt(if_stmt);
    mod.add_stmt(stmt_list);

    transform_if_to_case(&mod);
    auto stmt = reinterpret_cast<Stmt *>(mod.get_child(0)->get_child(0));
    EXPECT_TRUE(stmt->type() == StatementType::Switch);
    auto switch_ = stmt->as<SwitchStmt>();
    EXPECT_EQ(switch_->body().size(), 3);
    EXPECT_TRUE(switch_->body().find(nullptr) != switch_->body().end());

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

    auto &mod4 = c.generator("module4");
    mod4.port(PortDirection::In, "in", 1);
    mod4.port(PortDirection::Out, "out", 1);
    mod4.port(PortDirection::Out, "out2", 1);

    mod1.add_child_generator("inst0", mod2.shared_from_this());
    mod1.add_stmt(in2.assign(in1));
    mod1.add_stmt(out1.assign(out2));

    auto &mod5 = c.generator("module5");
    mod5.port(PortDirection::Out, "in", 1);
    mod5.port(PortDirection::Out, "out", 1);

    auto &mod6 = c.generator("module6");
    mod6.port(PortDirection::In, "in", 1, PortType::Clock);
    mod6.port(PortDirection::Out, "out", 1);

    EXPECT_THROW(mod1.replace(mod2.instance_name, mod3.shared_from_this()), VarException);
    EXPECT_THROW(mod1.replace(mod2.instance_name, mod4.shared_from_this()), VarException);
    EXPECT_THROW(mod1.replace(mod2.instance_name, mod5.shared_from_this()), VarException);
    EXPECT_THROW(mod1.replace(mod2.instance_name, mod6.shared_from_this()), VarException);
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
    auto &mod2 = c.generator("module2");
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
    auto &mod2 = c.generator("module2");
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
    auto def = PortBundleDefinition("bundle");
    def.add_definition("a", 1, 1, false, PortDirection::In, PortType::Data);
    def.add_definition("b", 1, 1, false, PortDirection::In, PortType::Data);
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
    mod3.add_bundle_port_def("p", def.flip());
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
    auto &mod = c.generator("mod");
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
    mod.add_stmt(out.assign(constant(0, 1).concat(in), AssignmentType::Blocking));

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

    mod1.add_stmt(out2.assign(in1 + var, AssignmentType::Blocking));

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
    auto &mod = c.generator("mod");
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
    auto &mod = c.generator("mod");
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

TEST(generator, latch_rst) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");
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
    for (auto mod : mods) {
        mod1.add_child_generator("mod" + std::to_string(count++), mod->shared_from_this());
    }
    for (auto const &in : inputs) {
        mod1.add_stmt(in->assign(port1_1));
    }
    mod1.add_stmt(port1_2.assign(port2_2 ^ port3_2 ^ port4_2));
    fix_assignment_type(&mod1);
    decouple_generator_ports(&mod1);
    fix_assignment_type(&mod1);
    hash_generators_sequential(&mod1);
    auto result = generate_verilog(&mod1);
    auto mod_src = result.at("parent");
    EXPECT_TRUE(mod_src.find("mod0_out ^ mod1_out ^ mod2_out") != std::string::npos);
}

TEST(generator, parameter_value) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");
    auto &p = mod.parameter("P", 4);
    p.set_value(4);
    auto &mod_in = mod.var("in", 4);
    auto &mod_out = mod.var("out", 4);
    for (auto const &port : {&mod_in, &mod_out}) {
        port->set_width_param(&p);
    }

    auto &child = c.generator("child");
    auto &p2 = child.parameter("P2", 4);
    p2.set_value(4);
    auto &child_in = child.port(PortDirection::In, "in", 4);
    auto &child_out = child.port(PortDirection::Out, "out", 4);
    child.add_stmt(child_out.assign(child_in));
    for (auto const &port : {&child_in, &child_out}) {
        port->set_width_param(&p2);
    }
    // wiring
    mod.add_stmt(child_in.assign(mod_in));
    mod.add_stmt(mod_out.assign(child_out));

    // set chaining
    p2.set_value(p.as<Param>());
    // change parent param value
    p.set_value(2);

    // run passes
    fix_assignment_type(&mod);
    verify_assignments(&mod);
    create_module_instantiation(&mod);
    generate_verilog(&mod);
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

TEST(pass, convert_wire_always_comb) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");
    auto &out = mod.var("out", 1);
    auto &in = mod.var("in", 1);
    auto assign = out.assign(in);
    mod.add_stmt(assign);
    convert_continuous_stmt(&mod);

    EXPECT_EQ(mod.stmts_count(), 1);
    auto const &stmt = mod.get_stmt(0);
    EXPECT_EQ(stmt->type(), StatementType::Block);
    auto block = stmt->as<StmtBlock>();
    EXPECT_EQ(block->block_type(), StatementBlockType::Combinational);
    EXPECT_EQ(block->get_stmt(0), assign);
}

TEST(enum_, duplicated_name) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");
    mod.enum_("E1", {{"A", 1}, {"B", 2}}, 2);
    EXPECT_THROW(mod.enum_("E2", {{"A", 1}}, 1), UserException);
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

TEST(debug, mock_hierarchy) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");
    mod.instance_name = "mod1.mod2.mod3";
    mock_hierarchy(&mod, "dut");
    EXPECT_EQ(c.get_generators_by_name("dut").size(), 1);
    EXPECT_EQ(mod.instance_name, "mod3");
    auto p = mod.parent_generator();
    EXPECT_TRUE(p != nullptr);
    EXPECT_EQ(p->instance_name, "mod2");
}

TEST(interface, wire_interface) {  // NOLINT
    Context c;
    auto &mod1 = c.generator("mod");
    auto config = std::make_shared<InterfaceDefinition>("Config");
    config->input("read", 1, 1);
    config->output("write", 1, 1);
    auto &read = mod1.port(PortDirection::In, "read", 1);
    auto &write = mod1.port(PortDirection::Out, "write", 1);
    auto i1 = mod1.interface(config, "bus1", false);
    mod1.add_stmt(i1->port("read").assign(read));
    mod1.add_stmt(write.assign(i1->port("write")));

    auto &mod2 = c.generator("mod2");
    auto i2 = mod2.interface(config, "bus", true);
    mod2.add_stmt(i2->port("write").assign(i2->port("read")));
    mod1.add_child_generator("inst", mod2.shared_from_this());

    EXPECT_NO_THROW(mod1.wire_interface(i1, i2));
    EXPECT_NO_THROW(verify_generator_connectivity(&mod1));
    EXPECT_NO_THROW(create_interface_instantiation(&mod1));
    EXPECT_NO_THROW(decouple_generator_ports(&mod1));
    EXPECT_EQ(mod1.stmts_count(), 1);

    auto result = extract_interface_info(&mod1);
    EXPECT_TRUE(!result.empty());
    EXPECT_TRUE(result.find("Config") != result.end());
    EXPECT_EQ(result.at("Config"),
              "interface Config(\n  input logic read,\n  output logic write\n);\nendinterface\n");
    fix_assignment_type(&mod1);
    create_module_instantiation(&mod1);
    result = generate_verilog(&mod1);
    EXPECT_TRUE(result.find("mod") != result.end());
}

TEST(interface, mod_port) {  // NOLINT
    Context c;
    auto &mod1 = c.generator("mod");
    auto config = std::make_shared<InterfaceDefinition>("Config");
    config->var("read", 1, 1);
    config->var("write", 1, 1);
    auto read = config->create_modport_def("R");
    auto write = config->create_modport_def("W");
    read->set_input("read");
    read->set_output("write");
    write->set_input("write");
    write->set_output("read");

    auto i1 = mod1.interface(config, "bus", false);
    auto &mod2 = c.generator("mod2");
    auto i2 = mod2.interface(read, "bus", true);
    mod2.add_stmt(i2->port("write").assign(i2->port("read")));
    mod1.add_child_generator("inst", mod2.shared_from_this());

    EXPECT_NO_THROW(mod1.wire_interface(i1->get_modport_ref("R"), i2));
    EXPECT_NO_THROW(verify_generator_connectivity(&mod1));
    EXPECT_NO_THROW(create_interface_instantiation(&mod1));
    EXPECT_NO_THROW(decouple_generator_ports(&mod1));

    auto result = extract_interface_info(&mod1);
    EXPECT_TRUE(!result.empty());
    EXPECT_TRUE(result.find("Config") != result.end());
    auto str = result.at("Config");
    EXPECT_TRUE(str.find("modport R(input read, output write)") != std::string::npos);

    fix_assignment_type(&mod1);
    create_module_instantiation(&mod1);
    result = generate_verilog(&mod1);
    EXPECT_TRUE(result.find("mod") != result.end());
    str = result.at("mod");
    EXPECT_TRUE(str.find(".bus(bus.R)\n") != std::string::npos);
    str = result.at("mod2");
    EXPECT_TRUE(str.find("Config.R bus\n") != std::string::npos);
}

TEST(interface, extract_interface_definition) {  // NOLINT
    Context c;
    auto &mod1 = c.generator("mod");
    auto config_0 = std::make_shared<InterfaceDefinition>("Config");
    auto &v = mod1.var("v", 1);
    config_0->input("read", 1, 1);
    config_0->output("write", 1, 1);
    auto i1 = mod1.interface(config_0, "bus1", false);
    auto config_1 = std::make_shared<InterfaceDefinition>("Config");
    config_1->input("read", 1, 1);
    config_1->output("write", 1, 1);
    config_1->output("write_", 1, 1);
    auto i2 = mod1.interface(config_1, "bus2", false);
    mod1.add_stmt(i1->port("read").assign(v));
    mod1.add_stmt(i2->port("read").assign(v));

    create_interface_instantiation(&mod1);
    EXPECT_THROW(extract_interface_info(&mod1), UserException);

    auto &mod2 = c.generator("mod");
    auto &v2 = mod2.var("v", 1);
    auto config_2 = std::make_shared<InterfaceDefinition>("Config");
    config_2->input("read", 1, 1);
    config_2->output("write", 1, 2);
    auto i3 = mod2.interface(config_1, "bus1", false);
    auto i4 = mod2.interface(config_2, "bus2", false);
    mod2.add_stmt(i3->port("read").assign(v2));
    mod2.add_stmt(i4->port("read").assign(v2));
    create_interface_instantiation(&mod2);
    EXPECT_THROW(extract_interface_info(&mod2), UserException);

    auto &mod3 = c.generator("mod");
    auto &v3 = mod3.var("v", 1);
    auto config_3 = std::make_shared<InterfaceDefinition>("Config");
    config_3->input("read", 1, 1);
    config_3->output("write", 1, 1);
    config_3->var("v", 1, 1);
    auto i5 = mod3.interface(config_1, "bus1", false);
    auto i6 = mod3.interface(config_3, "bus2", false);
    mod3.add_stmt(i5->port("read").assign(v3));
    mod3.add_stmt(i6->port("read").assign(v3));
    create_interface_instantiation(&mod3);
    EXPECT_THROW(extract_interface_info(&mod3), UserException);

    EXPECT_THROW(mod3.interface(config_1, "bus1", false), UserException);
}

TEST(pass, multiple_driver) {  // NOLINT
    Context c;
    auto &mod1 = c.generator("mod1");
    auto &out = mod1.port(PortDirection::Out, "out", 1);
    auto &in1 = mod1.port(PortDirection::In, "in1", 1);
    auto &in2 = mod1.port(PortDirection::In, "in2", 1);
    mod1.add_stmt(out.assign(in1));
    mod1.add_stmt(out.assign(in2));

    EXPECT_THROW(check_multiple_driver(&mod1), StmtException);

    // this won't trigger the check
    auto &mod2 = c.generator("mod2");
    auto &a2 = mod2.var("a2", 1);
    auto &b2 = mod2.var("b2", 1);
    auto comb = mod2.combinational();
    comb->add_stmt(a2.assign(constant(0, 1)));
    auto if_ = std::make_shared<IfStmt>(b2);
    comb->add_stmt(if_);
    if_->add_then_stmt(a2.assign(constant(1, 1)));
    fix_assignment_type(&mod2);

    EXPECT_NO_THROW(check_multiple_driver(&mod2));

    // this will trigger
    auto &mod3 = c.generator("mod3");
    auto &a3 = mod3.var("a2", 1);
    auto &b3 = mod3.var("b2", 1);
    auto seq3 = mod3.sequential();
    seq3->add_stmt(a3.assign(constant(0, 1)));
    auto if_3 = std::make_shared<IfStmt>(b3);
    seq3->add_stmt(if_3);
    if_3->add_then_stmt(a3.assign(constant(1, 1)));
    fix_assignment_type(&mod3);

    EXPECT_THROW(check_multiple_driver(&mod3), StmtException);

    // this will not trigger
    auto &mod4 = c.generator("mod4");
    auto &a4 = mod4.var("a4", 1);
    auto comb4 = mod4.combinational();
    comb->add_stmt(a4.assign(constant(0, 1)));
    comb->add_stmt(a4.assign(constant(1, 1)));
    fix_assignment_type(&mod4);
    EXPECT_NO_THROW(check_multiple_driver(&mod4));

    // this will not trigger
    auto &mod5 = c.generator("mod5");
    auto &a5 = mod4.var("a5", 1);
    auto &b5 = mod5.var("b5", 1);
    auto seq5 = mod5.sequential();
    auto if5 = std::make_shared<IfStmt>(b5);
    seq5->add_stmt(if5);
    if5->add_then_stmt(a5.assign(constant(0, 1)));
    if5->add_else_stmt(a5.assign(constant(0, 1)));
    fix_assignment_type(&mod5);
    EXPECT_NO_THROW(check_multiple_driver(&mod5));
}

TEST(pass, check_combinational_loop) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");
    auto &a = mod.var("a", 1);
    mod.add_stmt(a.assign(a + constant(1, 1)));
    fix_assignment_type(&mod);

    EXPECT_THROW(check_combinational_loop(&mod), StmtException);
}

TEST(stmt, raw_string_codegen) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");
    auto stmt = std::make_shared<RawStringStmt>("test\n");
    mod.add_stmt(stmt);
    auto result = generate_verilog(&mod);
    auto mod_str = result.at("mod");
    EXPECT_TRUE(mod_str.find("\ntest\n") != std::string::npos);
}

TEST(pass, extract_register_var_names) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");
    auto &a = mod.var("a", 1);
    auto &b = mod.var("b", 1);
    mod.add_stmt(a.assign(b));
    auto seq = std::make_shared<SequentialStmtBlock>();
    seq->add_stmt(b.assign(constant(1, 1)));
    mod.add_stmt(seq);

    fix_assignment_type(&mod);
    auto regs = extract_register_names(&mod);
    EXPECT_EQ(regs.size(), 1);
    EXPECT_EQ(regs[0], "mod.b");

    auto names = extract_var_names(&mod);
    EXPECT_EQ(names.size(), 2);
    EXPECT_TRUE(std::find(names.begin(), names.end(), "mod.b") != names.end());
}

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

TEST(formal, test_remove_async) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");
    auto &rst = mod.port(PortDirection::In, "rst", 1, PortType::AsyncReset);
    auto &var = mod.var("v", 1);
    auto var_rst = var.cast(VarCastType::AsyncReset);
    auto seq1 = mod.sequential();
    auto seq2 = mod.sequential();
    auto seq3 = mod.sequential();
    seq1->add_condition({BlockEdgeType::Negedge, rst.shared_from_this()});
    seq2->add_condition({BlockEdgeType::Negedge, var_rst});
    seq3->add_condition({BlockEdgeType::Negedge, rst.shared_from_this()});
    seq3->add_condition({BlockEdgeType::Negedge, var_rst});

    remove_async_reset(&mod);

    EXPECT_TRUE(seq1->get_conditions().empty());
    EXPECT_TRUE(seq2->get_conditions().empty());
    EXPECT_TRUE(seq3->get_conditions().empty());
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

TEST(pass, insert_clk_en) {  // NOLINT
    Context c;
    auto &parent = c.generator("parent");
    auto &clk = parent.port(PortDirection::In, "clk", 1, PortType::Clock);
    auto &rst = parent.port(PortDirection::In, "rst", 1, PortType::AsyncReset);
    auto &a = parent.port(PortDirection::Out, "a", 1);

    auto seq = parent.sequential();
    seq->add_condition({BlockEdgeType::Posedge, clk.shared_from_this()});
    seq->add_condition({BlockEdgeType::Posedge, rst.shared_from_this()});
    auto if_ = std::make_shared<IfStmt>(rst);
    if_->add_then_stmt(a.assign(constant(1, 1)));
    if_->add_else_stmt(a.assign(constant(0, 1)));
    seq->add_stmt(if_);

    // add child generator
    auto &child = c.generator("child");
    auto &clk_child = child.port(PortDirection::In, "clk", 1, PortType::Clock);
    auto child_seq = child.sequential();
    child_seq->add_condition({BlockEdgeType::Posedge, clk_child.shared_from_this()});
    child_seq->add_stmt(child.var("a", 1).assign(constant(1, 1)));
    child_seq->add_stmt(child.var("b", 1).assign(constant(1, 1)));

    // another child generator
    auto &child2 = c.generator("child2");
    auto &clk_child2 = child2.port(PortDirection::In, "clk", 1, PortType::Clock);
    auto &clk_en_child2 = child2.port(PortDirection::In, "clk_en", 1, PortType::ClockEnable);
    // always const
    child2.wire(clk_en_child2, constant(1, 1));
    auto child_seq2 = child2.sequential();
    child_seq2->add_condition({BlockEdgeType::Posedge, clk_child2.shared_from_this()});
    auto if_child2 = std::make_shared<IfStmt>(clk_en_child2);
    if_child2->add_then_stmt(child2.var("a", 1).assign(constant(1, 1)));
    child_seq2->add_stmt(if_child2);

    auto &child3 = c.generator("child3");
    auto &clk_child3 = child3.port(PortDirection::In, "clk", 1, PortType::Clock);
    auto &clk_en_child3 = child3.port(PortDirection::In, "clk_en", 1, PortType::ClockEnable);
    auto child_seq3 = child3.sequential();
    child_seq2->add_condition({BlockEdgeType::Posedge, clk_child3.shared_from_this()});
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
        seq_parent->add_condition({BlockEdgeType::Posedge, clk.shared_from_this()});
        auto if_seq_parent = std::make_shared<IfStmt>(rst);
        if_seq_parent->add_then_stmt(b.assign(constant(0, 1)));
        if_seq_parent->add_else_stmt(c_.assign(a));
        seq_parent->add_stmt(if_seq_parent);
    }

    // this is the one with both reset and clock enable
    {
        auto seq_parent = parent.sequential();
        seq_parent->add_condition({BlockEdgeType::Posedge, clk.shared_from_this()});
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
        seq_child->add_condition({BlockEdgeType::Posedge, clk_child.shared_from_this()});
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
        seq_child->add_condition({BlockEdgeType::Posedge, clk_child2.shared_from_this()});
        // same thing as the parent
        auto if_seq_child = std::make_shared<IfStmt>(rst_child2);
        if_seq_child->add_then_stmt(b_child.assign(constant(0, 1)));
        auto if__ = std::make_shared<IfStmt>(flush);
        if__->add_then_stmt(c_child.assign(constant(1, 1)));
        if__->add_else_stmt(c_child.assign(a_child));
        if_seq_child->add_else_stmt(if__);
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

TEST(codegen, yosys_src) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");

    auto attr = std::make_shared<Attribute>();
    attr->value_str = "yosys_src";
    mod.add_attribute(attr);

    auto &a = mod.var("a", 1);
    auto &b = mod.var("b", 1);
    auto stmt = a.assign(b);
    mod.add_stmt(stmt);

    std::string const filename = "test.cc";
    std::vector<IRNode*> nodes = {&a, &b, stmt.get()};
    for (uint32_t i = 0; i < 3; i++) {
        nodes[i]->fn_name_ln.emplace_back(std::make_pair(filename, i + 1));
    }

    fix_assignment_type(&mod);
    auto src = generate_verilog(&mod);
    auto mod_src = src.at("mod");
    EXPECT_NE(mod_src.find("(* src = \"test.cc:1\" *)"), std::string::npos);
    EXPECT_NE(mod_src.find("(* src = \"test.cc:3\" *)"), std::string::npos);
}

TEST(codegen, param_size_single_module) { // NOLINT
    Context c;
    auto &mod = c.generator("mod");

    auto &param = mod.parameter("P", 5);
    auto &in = mod.port(PortDirection::In, "in", 5, 3);
    auto &in2 = mod.port(PortDirection::In, "in2", 6, {3, 2});
    // create a slice
    in[2];
    // this should be an exception
    EXPECT_THROW(in.set_size_param(1, &param), UserException);
    param.set_value(1);
    EXPECT_THROW(in.set_size_param(0, &param), VarException);

    param.set_value(7);
    auto &new_param = param * constant(2, 5);
    EXPECT_NO_THROW(in.set_size_param(0, &new_param));
    EXPECT_NO_THROW(in2.set_size_param(1, &param));

    auto src = generate_verilog(&mod);
    auto mod_src = src.at("mod");
    EXPECT_NE(mod_src.find("input logic [4:0] in [(P * 5'h2)-1:0]"), std::string::npos);
    EXPECT_NE(mod_src.find("input logic [5:0] in2 [2:0][P-1:0]"), std::string::npos);
}

TEST(codegen, param_size_nested_module) {   // NOLINT
    Context c;
    auto &child = c.generator("child");
    auto &c_p = child.parameter("P_C", 32);
    // c_p has to have value
    c_p.set_value(1);
    auto &c_in = child.port(PortDirection::In, "in", 16, 32);
    c_in.set_size_param(0, &c_p);

    auto &parent = c.generator("parent");
    auto &p_p = parent.parameter("P", 32);
    auto &p_in = parent.port(PortDirection::In, "in", 16, 32);
    p_p.set_value(2);
    p_in.set_size_param(0, &p_p);

    parent.add_child_generator("inst", child);
    c_p.set_value(p_p.as<Param>());
    parent.add_stmt(c_in.assign(p_in));

    verify_assignments(&parent);
    verify_generator_connectivity(&parent);
    create_module_instantiation(&parent);

    auto src = generate_verilog(&parent);
    auto mod_src = src.at("parent");
    EXPECT_NE(mod_src.find(".P_C(P))"), std::string::npos);
    mod_src = src.at("child");
    EXPECT_NE(mod_src.find("input logic [15:0] in [P_C-1:0]"), std::string::npos);
}