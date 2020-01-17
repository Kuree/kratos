#ifndef KRATOS_FAULT_HH
#define KRATOS_FAULT_HH
#include "generator.hh"
#include "sim.hh"

namespace kratos {


class SimulationRun {
public:
    explicit SimulationRun(Generator *top): top_(top) {}

    void add_simulation_state(const std::map<std::string, int64_t> &values);
    void mark_wrong_value(const std::string &name);
    [[nodiscard]] bool has_wrong_value() const { return !wrong_value_.empty(); }

    // use simulator's logic to handle different states
    // FIXME: refactor out the state and the simulator
    Simulator *get_state(uint32_t index);
    [[nodiscard]] uint64_t num_states() const { return states_.size(); }

private:
    std::pair<Generator*, uint64_t> select_gen(const std::vector<std::string> &tokens);
    Var* select(const std::string &name);

    std::vector<std::unique_ptr<Simulator>> states_;
    Generator *top_;
    std::map<uint32_t, std::unordered_set<Var*>> wrong_value_;
};

class FaultAnalyzer {
public:
    explicit FaultAnalyzer(Generator *generator);
    // notice owner ship passing
    void add_simulation_run(const std::shared_ptr<SimulationRun> &run);
    [[nodiscard]] uint64_t num_runs() const { return runs_.size(); }
    std::unordered_set<Stmt*> compute_coverage(uint32_t index);
    std::unordered_set<Stmt*> compute_fault_stmts_from_coverage();

private:
    Generator *generator_;
    std::vector<std::shared_ptr<SimulationRun>> runs_;
    std::unordered_map<uint32_t, std::unordered_set<Stmt*>> coverage_maps_;
};

}  // namespace kratos

#endif  // KRATOS_FAULT_HH
