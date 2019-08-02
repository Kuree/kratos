#include "fsm.hh"
#include <fmt/format.h>
#include <cmath>
#include <utility>
#include "except.hh"
#include "generator.hh"

using fmt::format;
using std::runtime_error;

namespace kratos {

FSM::FSM(std::string name, kratos::Generator* generator)
    : fsm_name_(std::move(name)), generator_(generator) {
    // find the first clock signal
    auto vars = generator->get_ports(PortType::Clock);
    if (vars.empty()) {
        throw ::runtime_error("Unable to find any clock signal in " + generator->instance_name);
    }
    clk_ = generator_->get_port(vars[0]);
    // find the reset signal
    vars = generator->get_ports(PortType::AsyncReset);
    if (vars.empty()) {
        throw ::runtime_error("Unable to find any reset signal in " + generator->instance_name);
    }
    reset_ = generator_->get_port(vars[0]);
}

FSM::FSM(std::string name, kratos::Generator* generator, std::shared_ptr<Var> clk,
         std::shared_ptr<Var> reset)
    : fsm_name_(std::move(name)),
      generator_(generator),
      clk_(std::move(clk)),
      reset_(std::move(reset)) {}

void FSM::realize() {
    // generate the statements to the generator
    // first, get state and next state variable
    // compute number of states
    uint64_t num_states = states_.size();
    if (!num_states)
        throw ::runtime_error(::format("FSM {0} is empty", fsm_name()));
    uint32_t size = std::ceil(std::log2(num_states));
    (void)size;
}

void FSM::output(const std::string& var_name) {
    auto var = generator_->get_var(var_name);
    output(var);
}

void FSM::output(const std::shared_ptr<Var>& var) {
    if (!var) throw ::runtime_error(::format("var not found in {0}", generator_->instance_name));
    // very strict checking of ownership
    if (var->parent() != generator_) {
        if (var->parent()->parent() != generator_)
            throw VarException("FSM output has to be scoped inside the top-level of generator",
                               {var.get()});
    }
    outputs_.emplace(var.get());
}

std::shared_ptr<FSMState> FSM::add_state(const std::string& name) {
    if (states_.find(name) != states_.end())
        throw ::runtime_error(::format("{0} already exists in the FSM", name));
    auto ptr = std::make_shared<FSMState>(name, this);
    states_.emplace(name, ptr);
    state_names_.emplace_back(name);
    return ptr;
}

std::shared_ptr<FSMState> FSM::get_state(const std::string& name) {
    if (states_.find(name) == states_.end())
        throw ::runtime_error(::format("Cannot find {0} in the FSM", name));
    return states_.at(name);
}

void FSM::set_default_state(const std::string& name) { set_default_state(get_state(name)); }

void FSM::set_default_state(const std::shared_ptr<FSMState>& state) { default_state_ = state; }

FSMState::FSMState(std::string name, FSM* parent) : name_(std::move(name)), parent_(parent) {}

void FSMState::next(const std::shared_ptr<FSMState>& next_state, std::shared_ptr<Var>& cond) {
    auto ptr = cond.get();
    auto state_ptr = next_state.get();
    if (transitions_.find(ptr) != transitions_.end()) {
        throw ::runtime_error(::format("{0} has been added to FSM {1}-{2} already",
                                       ptr->to_string(), parent_->fsm_name(), name_));
    }
    transitions_.emplace(ptr, state_ptr);
}

void FSMState::output(const std::shared_ptr<Var>& output_var,
                      const std::shared_ptr<Var>& value_var) {
    auto output = output_var.get();
    auto value = value_var.get();
    if (output_values_.find(output) != output_values_.end()) {
        throw VarException(::format("{0} already has specified output"),
                           {output_values_.at(output)});
    }
    output_values_.emplace(output, value);
}

void FSMState::check_outputs() {
    auto outputs = parent_->outputs();
    for (auto const& output : outputs) {
        if (output_values_.find(output) == output_values_.end()) {
            throw VarException(::format("{0} not specified", output->to_string()), {output});
        }
    }
}

}