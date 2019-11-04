#ifndef KRATOS_SIM_HH
#define KRATOS_SIM_HH
#include "generator.hh"
#include <optional>
#include <queue>

namespace kratos {
class Simulator {
public:
    explicit Simulator(Generator *generator);
    void set_value(Var* var, std::optional<uint64_t> op_value);
    void set_complex_value(Var* var, const std::optional<std::vector<uint64_t>> &op_value);
    std::optional<uint64_t> get_value(Var *var) const;
    std::optional<std::vector<uint64_t>> get_complex_value(Var *var) const;

    void eval();

private:
    std::unordered_map<Var*, uint64_t> values_;
    std::unordered_map<Var*, std::vector<uint64_t>> complex_values_;
    std::queue<Stmt*> event_queue_;
    std::unordered_map<Var*, std::unordered_set<Stmt*>> dependency_;

    std::vector<std::pair<uint32_t, uint32_t>> get_slice_index(Var* var) const;
    void trigger_event(Var *var);

    void process_stmt(Stmt* stmt);
    void process_stmt(IfStmt *) {}
    void process_stmt(SwitchStmt *) {}
    void process_stmt(AssignStmt * stmt);
    void process_stmt(AssignStmt *stmt, std::unordered_map<Var*, std::vector<uint64_t>> &values);
    void process_stmt(CombinationalStmtBlock *) {}
    void process_stmt(SequentialStmtBlock *) {}


    std::optional<std::vector<uint64_t>> eval_expr(Var *var);
};
}  // namespace kratos

#endif  // KRATOS_SIM_HH
