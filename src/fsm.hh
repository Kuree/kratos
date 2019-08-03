#ifndef KRATOS_FSM_HH
#define KRATOS_FSM_HH

#include "stmt.hh"

namespace kratos {
class FSMState;

class FSM {
public:
    FSM(std::string name, Generator *generator);
    FSM(std::string name, Generator *generator, std::shared_ptr<Var> clk, std::shared_ptr<Var> reset);

    std::shared_ptr<FSMState> add_state(const std::string &name);
    std::shared_ptr<FSMState> get_state(const std::string &name);
    void set_start_state(const std::string &name);
    void set_start_state(const std::shared_ptr<FSMState> &state);

    // specify the state machine outputs and inputs
    void output(const std::string &var_name);
    void output(const std::shared_ptr<Var> &var);

    const std::string &fsm_name() const { return fsm_name_; }
    const std::unordered_set<Var*> &outputs() const { return outputs_; }

    void realize();
    // dot graph
    std::string dot_graph();
    void dot_graph(const std::string &filename);

    Generator* generator() { return generator_; }

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
};

class FSMState : public std::enable_shared_from_this<FSMState> {
public:
    FSMState(std::string name, FSM *parent);

    void next(const std::shared_ptr<FSMState> &next_state, std::shared_ptr<Var> &cond);
    void output(const std::shared_ptr<Var> &output_var, const std::shared_ptr<Var> &value_var);
    void output(const std::shared_ptr<Var> &output_var, int64_t value);
    void check_outputs();

    const inline std::string &name() { return name_; }
    const inline std::map<Var*, FSMState*> &transitions() { return transitions_; }
    const inline std::map<Var*, Var*> &output_values() const { return output_values_; }

private:
    std::string name_;
    FSM *parent_;
    std::map<Var*, FSMState*> transitions_;
    std::map<Var*, Var*> output_values_;
};
}  // namespace kratos

#endif  // KRATOS_FSM_HH
