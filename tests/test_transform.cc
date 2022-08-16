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

TEST(pass, decouple2) {  // NOLINT
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
    for (auto *mod : mods) {
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

TEST(pass, bundle_to_struct) {  // NOLINT
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