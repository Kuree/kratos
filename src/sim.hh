#ifndef KRATOS_SIM_HH
#define KRATOS_SIM_HH
#include "generator.hh"
#include <optional>
#include <queue>

namespace kratos {
constexpr uint64_t MAX_SIMULATION_DEPTH = 0xFFFFFFFF;
class Simulator {
public:
    explicit Simulator(Generator *generator);

    // public facing set and get values
    void set(Var* var, std::optional<uint64_t> value);
    void set(Var* var, const std::optional<std::vector<uint64_t>> &value);
    std::optional<uint64_t> get(Var *var) const;
    std::optional<std::vector<uint64_t>> get_array(Var *var) const;

    void eval();

protected:
    void set_value_(Var* var, std::optional<uint64_t> op_value);
    void set_complex_value_(Var* var, const std::optional<std::vector<uint64_t>> &op_value);
    std::optional<uint64_t> get_value_(Var *var) const;
    std::optional<std::vector<uint64_t>> get_complex_value_(Var *var) const;

private:
    std::unordered_map<Var*, uint64_t> values_;
    std::unordered_map<Var*, std::vector<uint64_t>> complex_values_;
    std::queue<Stmt*> event_queue_;
    std::unordered_map<Var*, std::unordered_set<Stmt*>> dependency_;
    // linked dependency is for partial updates
    std::unordered_map<Var*, std::unordered_map<uint32_t, Var*>> linked_dependency_;
    // this is prevent self triggering in always block
    std::unordered_set<Stmt*> scope_;

    std::vector<std::pair<uint32_t, uint32_t>> get_slice_index(Var* var) const;
    void trigger_event(Var *var, const std::unordered_set<uint32_t> &bit_mask);

    void process_stmt(Stmt* stmt);
    void process_stmt(IfStmt * if_);
    void process_stmt(SwitchStmt *switch_);
    void process_stmt(AssignStmt * stmt);
    void process_stmt(StmtBlock *block);

    void process_stmt(CombinationalStmtBlock *block);
    void process_stmt(SequentialStmtBlock *block);

    std::optional<std::vector<uint64_t>> eval_expr(Var *var);
    std::unordered_map<Var*, std::vector<uint64_t>> nba_values_;

    uint64_t simulation_depth_ = 0;
};
}  // namespace kratos

#endif  // KRATOS_SIM_HH
