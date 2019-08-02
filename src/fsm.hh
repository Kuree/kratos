#ifndef KRATOS_FSM_HH
#define KRATOS_FSM_HH

#include "stmt.hh"

namespace kratos {
class FSMState;

class FSM {
public:
    explicit FSM(const std::string &name);

    std::shared_ptr<FSMState> add_state(const std::string &name);

    std output();
    void input();

private:
};

class FSMState : public std::enable_shared_from_this<FSMState> {
public:
    explicit FSMState(const std::string &name);

    void next(const std::shared_ptr<FSMState> &next_state, std::shared_ptr<Var> &cond);

    void output(const std::shared_ptr<Var> &output_var, const std::shared_ptr<Var> &value);

private:
    std::map<std::shared_ptr<Var>, FSMState> transitions_;
};
}  // namespace kratos

#endif  // KRATOS_FSM_HH
