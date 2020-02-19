#include "../src/debug.hh"
#include "../src/except.hh"
#include "../src/generator.hh"
#include "../src/pass.hh"
#include "../src/stmt.hh"
#include "gtest/gtest.h"

using namespace kratos;

std::shared_ptr<Context> context() { return std::make_shared<Context>(); }

TEST(debug, inst) {  // NOLINT
    auto c_ptr = context();
    auto &c = *c_ptr;
    auto create_mod = [&]() -> Generator & {
        auto &mod = c.generator("mod");
        auto &in = mod.port(PortDirection::In, "in", 1);
        auto &out = mod.port(PortDirection::Out, "out", 1);
        mod.add_stmt(out.assign(in));
        return mod;
    };

    auto &mod1 = create_mod();
    auto &mod2 = create_mod();
    auto mods = {&mod1, &mod2};
    auto &mod = c.generator("parent");
    auto &input = mod.port(PortDirection::In, "in", 1);
    auto &output = mod.port(PortDirection::Out, "out", 1);
    uint32_t count = 0;
    for (auto &m : mods) {
        mod.add_child_generator("mod_" + std::to_string(count++), m->shared_from_this());
        mod.add_stmt(m->get_port("in")->assign(input));
    }
    mod.add_stmt(output.assign((*mod1.get_port("out")) & (*mod2.get_port("out"))));

    // passes
    remove_fanout_one_wires(&mod);
    decouple_generator_ports(&mod);
    fix_assignment_type(&mod);
    verify_generator_connectivity(&mod);

    convert_continuous_stmt(&mod);
    inject_instance_ids(&mod);
    inject_debug_break_points(&mod);

    hash_generators_parallel(&mod);
    uniquify_generators(&mod);
    create_module_instantiation(&mod);
    auto src = generate_verilog(&mod);
    EXPECT_TRUE(src.find("parent") != src.end());
    auto code = src.at("parent");
    printf("%s\n", code.c_str());
    EXPECT_TRUE(code.find("unq") == std::string::npos);
}

TEST(debug, clock_breakpoint) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");
    mod.port(PortDirection::In, "clk", 1, PortType::Clock);
    inject_clock_break_points(&mod);
    // test if it has the inserted block
    EXPECT_EQ(mod.stmts_count(), 1);
    EXPECT_TRUE(mod.get_stmt(0)->type() == StatementType::Block);
    auto block = mod.get_stmt(0)->as<StmtBlock>();
    EXPECT_EQ(block->size(), 1);
    EXPECT_EQ(block->block_type(), StatementBlockType::Sequential);
    EXPECT_EQ((*block)[0]->type(), StatementType::FunctionalCall);
}