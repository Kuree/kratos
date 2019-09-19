#ifndef KRATOS_FSM_HH
#define KRATOS_FSM_HH

#include "stmt.hh"

namespace kratos {
class FSMState;

class FSM {
public:
    FSM(std::string name, Generator *generator);
    FSM(std::string name, Generator *generator, std::shared_ptr<Var> clk,
        std::shared_ptr<Var> reset);

    std::shared_ptr<FSMState> add_state(const std::string &name);
    std::shared_ptr<FSMState> add_state(const std::string &name,
                                        const std::pair<std::string, uint32_t> &debug_info);
    std::shared_ptr<FSMState> get_state(const std::string &name) const;
    void set_start_state(const std::string &name);
    void set_start_state(const std::shared_ptr<FSMState> &state);
    void set_start_state(const std::string &name, const std::pair<std::string, uint32_t> &debug);
    void set_start_state(const std::shared_ptr<FSMState> &state,
                         const std::pair<std::string, uint32_t> &debug);

    // specify the state machine outputs and inputs
    void output(const std::string &var_name);
    void output(const std::shared_ptr<Var> &var);

    const std::string &fsm_name() const { return fsm_name_; }
    const std::unordered_set<Var *> &outputs() const { return outputs_; }
    const std::map<std::string, std::shared_ptr<FSMState>> &states() const { return states_; }

    void realize();
    bool realized() const { return realized_; }
    // dot graph
    std::string dot_graph();
    void dot_graph(const std::string &filename);
    // output table
    std::string output_table();
    void output_table(const std::string &filename);

    Generator *generator() { return generator_; }

    // code gen style
    // either moore or mealy
    void set_moore(bool is_moore) { moore_ = is_moore; }
    bool is_moore() const { return moore_; }

    // nested FSM
    FSM *parent_fsm() const { return parent_fsm_; }
    void add_child_fsm(FSM *fsm);
    std::vector<FSMState *> get_all_child_states(bool include_extra_state = false) const;
    std::vector<FSM *> get_all_child_fsm() const;

private:
    std::string fsm_name_;
    Generator *generator_;
    std::unordered_set<Var *> outputs_;
    std::shared_ptr<Var> clk_ = nullptr;
    std::shared_ptr<Var> reset_ = nullptr;
    std::map<std::string, std::shared_ptr<FSMState>> states_;
    // use it to keep it in order
    std::vector<std::string> state_names_;
    std::shared_ptr<FSMState> start_state_ = nullptr;
    std::pair<std::string, uint32_t> start_state_debug_ = {"", 0};

    std::unordered_map<std::string, std::pair<std::string, uint32_t>> fn_name_ln_;

    bool realized_ = false;
    bool moore_ = true;

    void generate_state_transition(
        Enum &enum_def, EnumVar &current_state, EnumVar &next_state,
        const std::unordered_map<FSMState *, std::string> &state_name_mapping);
    void generate_output(Enum &enum_def, EnumVar &current_state,
                         const std::unordered_map<FSMState *, std::string> &state_name_mapping);
    std::shared_ptr<FunctionStmtBlock> get_func_def();
    std::shared_ptr<FunctionCallStmt> &get_func_call_stmt(
        const std::shared_ptr<FunctionStmtBlock> &func_def, const FSMState *fsm_state,
        std::shared_ptr<FunctionCallStmt> &func_stmt) const;

    FSM *parent_fsm_ = nullptr;
    std::map<std::string, FSM *> child_fsms_;
    std::shared_ptr<AssignStmt> get_next_state_stmt(
        Enum &enum_def, EnumVar &next_state, const FSMState *state, FSMState *next_fsm_state,
        const std::unordered_map<FSMState *, std::string> &state_name_mapping) const;
};

class FSMState : public std::enable_shared_from_this<FSMState> {
public:
    FSMState(std::string name, FSM *parent);

    void next(const std::shared_ptr<FSMState> &next_state, const std::shared_ptr<Var> &cond);
    void next(const std::shared_ptr<FSMState> &next_state, const std::shared_ptr<Var> &cond,
              const std::pair<std::string, uint32_t> &debug_info);
    void output(const std::shared_ptr<Var> &output_var, const std::shared_ptr<Var> &value_var);
    void output(const std::shared_ptr<Var> &output_var, int64_t value);
    void output(const std::shared_ptr<Var> &output_var, const std::shared_ptr<Var> &value_var,
                const std::pair<std::string, uint32_t> &debug_info);
    void output(const std::shared_ptr<Var> &output_var, int64_t value,
                const std::pair<std::string, uint32_t> &debug_info);
    void check_outputs();

    const inline std::string &name() const { return name_; }
    const inline std::map<Var *, FSMState *> &transitions() { return transitions_; }
    const inline std::map<Var *, Var *> &output_values() const { return output_values_; }
    std::string handle_name() const;

    // debug info
    const inline std::unordered_map<FSMState *, std::pair<std::string, uint32_t>>
        &next_state_fn_ln() const {
        return next_state_fn_ln_;
    }
    const inline std::unordered_map<Var *, std::pair<std::string, uint32_t>> &output_fn_ln() const {
        return output_fn_ln_;
    }

    const FSM *parent() const { return parent_; }

private:
    std::string name_;
    FSM *parent_;
    std::map<Var *, FSMState *> transitions_;
    std::map<Var *, Var *> output_values_;

    std::unordered_map<FSMState *, std::pair<std::string, uint32_t>> next_state_fn_ln_;
    std::unordered_map<Var *, std::pair<std::string, uint32_t>> output_fn_ln_;
};
}  // namespace kratos

#endif  // KRATOS_FSM_HH
