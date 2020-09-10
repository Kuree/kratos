#ifndef KRATOS_SIM_HH
#define KRATOS_SIM_HH
#include <optional>
#include <queue>
#include "generator.hh"

namespace kratos {
constexpr uint64_t MAX_SIMULATION_DEPTH = 0xFFFFFFFF;
class Simulator {
public:
    explicit Simulator(Generator *generator);

    // public facing set and get values
    void set(Var *var, std::optional<uint64_t> value, bool eval=true);
    void set_i(const Var *var, std::optional<int64_t> value, bool eval=true);
    void set(Var *var, const std::optional<std::vector<uint64_t>> &value, bool eval=true);
    void set_i(const Var *var, const std::optional<std::vector<int64_t>> &value, bool eval=true);
    std::optional<uint64_t> get(Var *var) const;
    std::optional<std::vector<uint64_t>> get_array(Var *var) const;

    void eval();
    std::optional<std::vector<uint64_t>> eval_expr(const Var *var) const;

    static uint64_t static_evaluate_expr(Var *expr);

protected:
    void set_value_(const Var *var, std::optional<uint64_t> op_value);
    void set_complex_value_(const Var *var, const std::optional<std::vector<uint64_t>> &op_value);
    std::optional<uint64_t> get_value_(const Var *var) const;
    std::optional<std::vector<uint64_t>> get_complex_value_(const Var *var) const;

private:
    std::unordered_map<const Var *, uint64_t> values_;
    std::unordered_map<const Var *, std::vector<uint64_t>> complex_values_;
    std::queue<std::pair<const Var *, Stmt *>> event_queue_;
    std::unordered_map<const Var *, std::unordered_set<Stmt *>> dependency_;
    // linked dependency is for partial updates
    std::unordered_map<const Var *, std::unordered_map<uint32_t, Var *>> linked_dependency_;
    // this is prevent self triggering in always block
    std::unordered_set<Stmt *> scope_;

    std::vector<std::pair<uint32_t, uint32_t>> get_slice_index(const Var *var) const;
    void trigger_event(const Var *var, const std::unordered_set<uint32_t> &bit_mask);

    void process_stmt(Stmt *stmt, const Var *var);
    void process_stmt(IfStmt *if_, const Var *var);
    void process_stmt(SwitchStmt *switch_, const Var *var);
    void process_stmt(AssignStmt *stmt, const Var *var);
    void process_stmt(StmtBlock *block, const Var *var);

    void process_stmt(CombinationalStmtBlock *block, const Var *);
    void process_stmt(SequentialStmtBlock *block, const Var *var);

    std::unordered_map<Var *, std::vector<uint64_t>> nba_values_;

    // pull-up registers
    void init_pull_up_value(Generator *generator);

    uint64_t simulation_depth_ = 0;
};
}  // namespace kratos

#endif  // KRATOS_SIM_HH
