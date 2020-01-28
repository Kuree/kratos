#include <fmt/format.h>

#include "../src/except.hh"
#include "../src/fault.hh"
#include "../src/generator.hh"
#include "../src/pass.hh"
#include "../src/stmt.hh"
#include "../src/util.hh"
#include "gtest/gtest.h"

using namespace kratos;
using fmt::format;

TEST(fault, count_stmt) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");
    auto &in = mod.port(PortDirection::In, "in", 4);
    auto &clk = mod.port(PortDirection::In, "clk", 1, 1, PortType::Clock, false);
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

std::pair<Generator &, SequentialStmtBlock *> create_verilator_mod(Context &c) {
    auto &mod = c.generator("mod");
    mod.debug = true;
    auto &in = mod.port(PortDirection::In, "in", 4);
    auto &clk = mod.port(PortDirection::In, "clk", 1, 1, PortType::Clock, false);
    auto &out = mod.port(PortDirection::Out, "out", 4);
    auto seq = std::make_shared<SequentialStmtBlock>();
    mod.add_stmt(seq);
    seq->add_condition({BlockEdgeType::Posedge, clk.shared_from_this()});
    auto if_ = std::make_shared<IfStmt>(in > constant(2, 4));
    if_->fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
    seq->add_stmt(if_);
    if_->then_body()->fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
    auto assign_0 = out.assign(constant(4, 4));
    assign_0->fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
    if_->add_then_stmt(assign_0);
    if_->else_body()->fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
    auto assign_1 = out.assign(out + in);
    assign_1->fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
    if_->add_else_stmt(assign_1);

    fix_assignment_type(&mod);
    return {mod, seq.get()};
}

TEST(fault, parse_verilog_cov_file) {  // NOLINT
    // const std::string filename = "cov.dat";
    Context c;
    auto iter = create_verilator_mod(c);
    auto &mod = iter.first;
    auto seq = iter.second;
    generate_verilog(&mod);
    // fake the output
    mod.verilog_fn = "mod.sv";

    auto if_ = seq->get_stmt(0)->as<IfStmt>();

    auto coverage = parse_verilator_coverage(&mod, "cov.dat");
    EXPECT_EQ(coverage.size(), 2);
    EXPECT_TRUE(coverage.find(if_->then_body().get()) != coverage.end());
    EXPECT_TRUE(coverage.find(if_->else_body().get()) != coverage.end());

    auto run = std::make_shared<SimulationRun>(&mod);
    run->add_simulation_coverage(coverage);
    FaultAnalyzer fault(&mod);
    fault.add_simulation_run(run);
    auto r = fault.compute_fault_stmts_from_coverage();
    EXPECT_TRUE(r.empty());
    auto cov = fault.compute_coverage(0);
    EXPECT_EQ(cov.size(), 2);
}

TEST(fault, produce_cov_xml) {  // NOLINT
    // const std::string filename = "cov.dat";
    Context c;
    auto iter = create_verilator_mod(c);
    auto &mod = iter.first;

    generate_verilog(&mod);
    // fake the output
    mod.verilog_fn = "mod.sv";

    auto coverage = parse_verilator_coverage(&mod, "cov.dat");
    auto run = std::make_shared<SimulationRun>(&mod);
    run->add_simulation_coverage(coverage);
    FaultAnalyzer fault(&mod);
    fault.add_simulation_run(run);
    fault.compute_fault_stmts_from_coverage();

    // we only does this test on linux
    // so it should be fine
    auto temp_dir = fs::temp_directory_path();
    std::string output_filename = fs::join(temp_dir, "cov.xml");
    fault.output_coverage_xml(output_filename);

    // read the input in
    std::ifstream in(output_filename);
    std::string content((std::istreambuf_iterator<char>(in)), std::istreambuf_iterator<char>());

    // make sure both if statements and assignments are covered
    auto seq = iter.second;
    auto if_ = seq->get_stmt(0)->as<IfStmt>();
    auto if_then_ln = if_->then_body()->fn_name_ln.front().second;
    auto if_else_ln = if_->else_body()->fn_name_ln.front().second;
    auto then_assign_ = if_->then_body()->get_stmt(0)->fn_name_ln.front().second;
    auto else_assign_ = if_->else_body()->get_stmt(0)->fn_name_ln.front().second;
    auto lns = {if_then_ln, if_else_ln, then_assign_, else_assign_};
    for (auto const &ln : lns) {
        EXPECT_TRUE(content.find(::format("number=\"{0}\" hits=\"1\"", ln)) != std::string::npos);
    }
}

TEST(fault, parse_icc_cov_file) {  // NOLINT
    Context c;
    auto &mod = c.generator("mod");
    mod.debug = true;
    mod.port(PortDirection::In, "in", 4);
    auto &sel = mod.port(PortDirection::In, "sel", 4);
    auto &out = mod.port(PortDirection::Out, "out", 4);
    mod.parameter("KRATOS_INSTANCE_ID", 32);

    auto comb = std::make_shared<CombinationalStmtBlock>();
    mod.add_stmt(comb);
    auto if_ = std::make_shared<IfStmt>(sel);
    comb->add_stmt(if_);
    if_->add_then_stmt(out.assign(constant(0, 4)));
    for (uint32_t i = 0; i < 4; i++) {
        if_->add_else_stmt(out[i].assign(constant(1, 1)));
    }

    fix_assignment_type(&mod);
    generate_verilog(&mod);
    // fake the output
    mod.verilog_fn = "test.sv";

    auto result = parse_icc_coverage(&mod, "icc_cov.txt");
    EXPECT_EQ(result.size(), 2);
    for (auto const &iter : result) {
        EXPECT_TRUE(iter.first->type() == StatementType::Block);
    }
}