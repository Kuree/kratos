#include "../src/pass.hh"
#include "../src/except.hh"
#include "../src/fault.hh"
#include "../src/generator.hh"
#include "../src/stmt.hh"
#include "gtest/gtest.h"

using namespace kratos;

TEST(fault, count_stmt) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");
    auto &in = mod.port(PortDirection::In, "in", 4);
    auto &clk = mod.port(PortDirection::In, "rst", 1, 1, PortType::Clock, false);
    auto &out = mod.port(PortDirection::Out, "out", 4);
    auto seq = std::make_shared<SequentialStmtBlock>();
    mod.add_stmt(seq);
    seq->add_condition({BlockEdgeType::Posedge, clk.shared_from_this()});
    auto if_ = std::make_shared<IfStmt>(in > constant(2, 4));
    seq->add_stmt(if_);
    if_->add_then_stmt(out.assign(constant(4, 4)));
    if_->add_else_stmt(out.assign(out + in));

    fix_assignment_type(&mod);

    std::map<std::string, int64_t> correct_state0 = {{"mod.in", 1}, {"mod.out", 0}};
    std::map<std::string, int64_t> correct_state1 = {{"mod.in", 1}, {"mod.out", 1}};
    std::map<std::string, int64_t> correct_state2 = {{"mod.in", 2}, {"mod.out", 2}};

    auto correct_run = std::make_shared<SimulationRun>(&mod);
    correct_run->add_simulation_state(correct_state0);
    correct_run->add_simulation_state(correct_state1);
    correct_run->add_simulation_state(correct_state2);

    std::map<std::string, int64_t> wrong_state0 = {{"mod.in", 1}, {"mod.out", 0}};
    std::map<std::string, int64_t> wrong_state1 = {{"mod.in", 2}, {"mod.out", 1}};
    std::map<std::string, int64_t> wrong_state2 = {{"mod.in", 3}, {"mod.out", 0}};
    auto wrong_run = std::make_shared<SimulationRun>(&mod);
    wrong_run->add_simulation_state(wrong_state0);
    wrong_run->add_simulation_state(wrong_state1);
    wrong_run->add_simulation_state(wrong_state2);
    wrong_run->mark_wrong_value("mod.out");

    FaultAnalyzer fault(&mod);
    fault.add_simulation_run(correct_run);
    fault.add_simulation_run(wrong_run);

    auto result = fault.compute_fault_stmts_from_coverage();
    EXPECT_EQ(result.size(), 1);

}