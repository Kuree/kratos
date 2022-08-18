#include "../src/codegen.hh"
#include "../src/context.hh"
#include "../src/generator.hh"
#include "../src/pass.hh"
#include "../src/stmt.hh"
#include "../src/tb.hh"
#include "gtest/gtest.h"

using namespace kratos;

TEST(test_tb, code_gen) {  // NOLINT
    Context context;
    Generator &gen = context.generator("mod");
    auto &dut_in = gen.port(PortDirection::In, "in", 1);
    auto &dut_out = gen.port(PortDirection::Out, "out", 1);
    gen.add_stmt(dut_out.assign(dut_in));

    // test bench
    TestBench tb(&context, "TOP");
    tb.add_child_generator("dut", gen.shared_from_this());
    auto &in = tb.var("in", 1);
    auto &out = tb.var("out", 1);

    tb.wire(dut_in, in);
    tb.wire(out, dut_out);

    // add sequence
    // add a clock
    auto &clk = tb.var("clk", 1);
    auto seq = std::make_shared<Sequence>(in.eq(constant(1, 1)).shared_from_this());
    seq->imply(out.eq(constant(1, 1)).shared_from_this());
    auto property = tb.property("fixed_value", seq);
    property->edge(BlockEdgeType::Posedge, clk.shared_from_this());

    auto *top_ = &tb;
    EXPECT_NO_THROW({
        fix_assignment_type(top_);
        create_module_instantiation(top_);
        verify_generator_connectivity(top_);

        // code gen the module top
        SystemVerilogCodeGen code_gen(top_);
        code_gen.str();
    });
}