#include "../src/codegen.hh"
#include "../src/fsm.hh"
#include "../src/generator.hh"
#include "../src/interface.hh"
#include "../src/util.hh"
#include "gtest/gtest.h"

using namespace kratos;

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