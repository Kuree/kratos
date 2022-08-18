#include "../src/codegen.hh"
#include "../src/debug.hh"
#include "../src/except.hh"
#include "../src/formal.hh"
#include "../src/fsm.hh"
#include "../src/generator.hh"
#include "../src/interface.hh"
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
    mod = (Generator::from_verilog(&c, "module1.sv", "module4", {}, {}));
    EXPECT_TRUE(mod.get_port("input_port") != nullptr);
    EXPECT_TRUE(mod.get_port("output_port") != nullptr);
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

TEST(enum_, duplicated_name) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");
    mod.enum_("E1", {{"A", 1}, {"B", 2}}, 2);
    EXPECT_THROW(mod.enum_("E2", {{"A", 1}}, 1), UserException);
}

TEST(debug, mock_hierarchy) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");
    mod.instance_name = "mod1.mod2.mod3";
    mock_hierarchy(&mod, "dut");
    EXPECT_EQ(c.get_generators_by_name("dut").size(), 1);
    EXPECT_EQ(mod.instance_name, "mod3");
    auto const *p = mod.parent_generator();
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

TEST(formal, test_remove_async) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");
    auto &rst = mod.port(PortDirection::In, "rst", 1, PortType::AsyncReset);
    auto &var = mod.var("v", 1);
    auto var_rst = var.cast(VarCastType::AsyncReset);
    auto seq1 = mod.sequential();
    auto seq2 = mod.sequential();
    auto seq3 = mod.sequential();
    seq1->add_condition({EventEdgeType::Negedge, rst.shared_from_this()});
    seq2->add_condition({EventEdgeType::Negedge, var_rst});
    seq3->add_condition({EventEdgeType::Negedge, rst.shared_from_this()});
    seq3->add_condition({EventEdgeType::Negedge, var_rst});

    remove_async_reset(&mod);

    EXPECT_TRUE(seq1->get_event_controls().empty());
    EXPECT_TRUE(seq2->get_event_controls().empty());
    EXPECT_TRUE(seq3->get_event_controls().empty());
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
    in.set_is_packed(false);
    auto &in2 = mod.port(PortDirection::In, "in2", 6, {3, 2});
    in2.set_is_packed(false);
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
    c_in.set_is_packed(false);
    c_in.set_size_param(0, &c_p);

    auto &parent = c.generator("parent");
    auto &p_p = parent.parameter("P", 32);
    auto &p_in = parent.port(PortDirection::In, "in", 16, 32);
    p_in.set_is_packed(false);
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

TEST(codegen, copy_port_definition) {   // NOLINT
    Context c;
    auto &child = c.generator("child");
    auto &c_p = child.parameter("P_C", 32);
    // c_p has to have value
    c_p.set_value(1);
    auto &c_in = child.port(PortDirection::In, "in", 16, 32);
    c_in.set_is_packed(false);
    c_in.set_size_param(0, &(c_p * constant(2, 16)));

    auto &parent = c.generator("parent");
    auto &p_p = parent.parameter("P", 32);
    p_p.set_value(2);

    parent.add_child_generator("inst", child);

    c_p.set_value(p_p.as<Param>());
    // copy the definition from the child
    auto &p_in = parent.port(c_in);
    parent.add_stmt(c_in.assign(p_in));

    verify_assignments(&parent);
    verify_generator_connectivity(&parent);
    create_module_instantiation(&parent);

    auto src = generate_verilog(&parent);
    auto mod_src = src.at("parent");
    EXPECT_NE(mod_src.find("input logic [15:0] in [(P * 32'h2)-1:0]"), std::string::npos);
}

TEST(generator, unwire) {   // NOLINT
    Context c;
    auto &mod = c.generator("mod");
    auto &a = mod.var("a", 1);
    auto &b = mod.var("b", 1);

    mod.unwire(b, a);
    EXPECT_EQ(mod.stmts_count(), 0);

    mod.add_stmt(a.assign(b));
    EXPECT_EQ(mod.stmts_count(), 1);
    mod.unwire(b, a);
    EXPECT_EQ(mod.stmts_count(), 0);
}