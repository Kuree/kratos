#include "fsm.hh"
#include <fmt/format.h>
#include <cmath>
#include <fstream>
#include <sstream>
#include <utility>
#include "except.hh"
#include "generator.hh"

using fmt::format;
using std::endl;
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
    if (!num_states) throw ::runtime_error(::format("FSM {0} is empty", fsm_name()));
    uint32_t width = std::ceil(std::log2(num_states));
    // define a enum type
    std::map<std::string, uint64_t> raw_def;
    uint64_t count = 0;
    std::string start_state_name;
    for (auto const& iter : states_) {
        if (start_state_name.empty()) start_state_name = iter.first;
        raw_def.emplace(iter.first, count++);
        // check states
        iter.second->check_outputs();
    }
    auto& enum_def = generator_->enum_(fsm_name_ + "_state", raw_def, width);
    // create two state variable, current_state, and next_state
    auto current_state_name = generator_->get_unique_variable_name(fsm_name_, "current_state");
    auto next_state_name = generator_->get_unique_variable_name(fsm_name_, "next_state");
    auto& current_state = generator_->enum_var(current_state_name, enum_def.shared_from_this());
    auto& next_state = generator_->enum_var(next_state_name, enum_def.shared_from_this());

    // sequential logic
    // if (reset)
    //   current_state <= default_state
    // else
    //   current_state <= next_state
    auto seq = generator_->sequential();
    seq->add_condition({BlockEdgeType::Posedge, clk_});
    seq->add_condition({BlockEdgeType ::Posedge, reset_});
    if (!start_state_) {
        // pick a random one?
        start_state_ = get_state(start_state_name);
    }
    auto seq_if = std::make_shared<IfStmt>(reset_);
    seq_if->add_then_stmt(
        current_state.assign(enum_def.get_enum(start_state_->name()), AssignmentType::NonBlocking));
    seq_if->add_else_stmt(current_state.assign(next_state.shared_from_this(), NonBlocking));
    // add it to the seq
    seq->add_stmt(seq_if);

    // combination logic to compute next state
    auto state_comb = generator_->combinational();
    auto case_state_comb = std::make_shared<SwitchStmt>(current_state.shared_from_this());
    for (auto const& [state_name, state] : states_) {
        // a list of if statements
        std::shared_ptr<IfStmt> if_ = nullptr;
        std::shared_ptr<IfStmt> top_if = nullptr;
        std::vector<Var*> vars;
        auto transitions = state->transitions();
        vars.reserve(transitions.size());
        for (auto const& iter : transitions) vars.emplace_back(iter.first);
        std::sort(vars.begin(), vars.end(), [=](const auto& lhs, const auto& rhs) {
            return transitions.at(lhs)->name() < transitions.at(rhs)->name();
        });
        for (auto const& cond : vars) {
            auto next_fsm_state = transitions.at(cond);
            if (!if_) {
                if_ = std::make_shared<IfStmt>(cond->shared_from_this());
                if_->add_then_stmt(
                    next_state.assign(enum_def.get_enum(next_fsm_state->name()), Blocking));
                top_if = if_;
            } else {
                auto new_if = std::make_shared<IfStmt>(cond->shared_from_this());
                new_if->add_then_stmt(
                    next_state.assign(enum_def.get_enum(next_fsm_state->name()), Blocking));
                if_->add_else_stmt(new_if);
                if_ = new_if;
            }
        }
        if (!top_if) throw ::runtime_error("Unable to find any state transition");
        case_state_comb->add_switch_case(enum_def.get_enum(state_name), top_if);
    }

    // add it to the state_comb
    state_comb->add_stmt(case_state_comb);

    // now the output logic
    auto output_comb = generator_->combinational();
    auto output_case_comb = std::make_shared<SwitchStmt>(current_state.shared_from_this());
    for (auto const& [state_name, state] : states_) {
        std::vector<std::shared_ptr<Stmt>> stmts;
        auto const& output_values = state->output_values();
        stmts.reserve(output_values.size());
        // sort the names
        std::vector<Var*> vars;
        vars.reserve(output_values.size());
        for (auto const& iter : output_values) vars.emplace_back(iter.first);
        std::sort(vars.begin(), vars.end(),
                  [](auto& lhs, auto& rhs) { return lhs->name < rhs->name; });
        for (auto const& output_var : vars) {
            auto value = output_values.at(output_var);
            if (value) {
                // value can be a nullptr
                stmts.emplace_back(output_var->assign(value->shared_from_this()));
            }
        }
        // add it to the case
        output_case_comb->add_switch_case(enum_def.get_enum(state_name), stmts);
    }

    // add it to the output_comb
    output_comb->add_stmt(output_case_comb);
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

void FSM::set_start_state(const std::string& name) { set_start_state(get_state(name)); }

void FSM::set_start_state(const std::shared_ptr<FSMState>& state) { start_state_ = state; }

std::string FSM::dot_graph() {
    constexpr char indent[] = "    ";
    std::stringstream stream;

    // header
    stream << "digraph " << fsm_name_ << " {" << endl;
    stream << indent << "rankdir=LR;" << ::endl << ::endl;

    // start state is double circle
    std::string start_state_name;
    if (start_state_) start_state_name = start_state_->name();
    if (!start_state_name.empty())
        stream << indent
               << ::format("node [shape = doublecircle, label=\"{0}\"] {0};", start_state_->name())
               << ::endl;
    // the rest of the states
    for (auto const& iter : states_) {
        auto state_name = iter.first;
        if (state_name == start_state_name) continue;
        stream << indent << ::format("node [shape = circle, label=\"{0}\"] {0};", state_name)
               << ::endl;
    }

    stream << ::endl;
    // state transition
    for (auto const& [state_name, state] : states_) {
        auto transitions = state->transitions();
        // deterministic sorting
        std::vector<Var*> conds;
        conds.reserve(transitions.size());
        for (auto const& iter : transitions) conds.emplace_back(iter.first);
        std::sort(conds.begin(), conds.end(), [](auto const& lhs, auto const& rhs) {
            return lhs->to_string() < rhs->to_string();
        });
        for (auto const& cond : conds) {
            auto next_state = transitions.at(cond);
            stream << indent
                   << ::format("{0}    ->  {1} [ label = \"{2}\" ];", state_name,
                               next_state->name(), cond->to_string())
                   << ::endl;
        }
    }
    stream << "}" << ::endl;

    return stream.str();
}

void FSM::dot_graph(const std::string& filename) {
    std::ofstream stream(filename);
    stream << dot_graph();
    stream.close();
}

std::string FSM::output_table() {
    std::stringstream stream;
    // sort the outputs
    std::vector<Var*> outputs;
    outputs.reserve(outputs_.size());
    for (auto const& var : outputs_) outputs.emplace_back(var);
    std::sort(outputs.begin(), outputs.end(),
              [](const auto& lhs, const auto& rhs) { return lhs->to_string() < rhs->to_string(); });
    // write the header
    stream << "State";
    for (const auto& var : outputs) stream << "," << var->to_string();
    stream << ::endl;

    // notice that we don't need to sort the state names since it's stored in map
    // which is ordered
    for (auto const& [state_name, state] : states_) {
        stream << state_name;
        for (auto const& output : outputs) {
            auto value = state->output_values().at(output);
            stream << "," << value->to_string();
        }
        stream << ::endl;
    }

    return stream.str();
}

void FSM::output_table(const std::string& filename) {
    std::ofstream stream(filename);
    stream << output_table();
    stream.close();
}

FSMState::FSMState(std::string name, FSM* parent) : name_(std::move(name)), parent_(parent) {}

void FSMState::next(const std::shared_ptr<FSMState>& next_state, std::shared_ptr<Var>& cond) {
    auto ptr = cond.get();
    if (cond->width != 1) throw VarException("Condition has to be a boolean value", {ptr});
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

void FSMState::output(const std::shared_ptr<Var>& output_var, int64_t value) {
    auto& c = parent_->generator()->constant(value, output_var->width, output_var->is_signed);
    output(output_var, c.shared_from_this());
}

void FSMState::check_outputs() {
    auto outputs = parent_->outputs();
    for (auto const& output : outputs) {
        if (output_values_.find(output) == output_values_.end()) {
            throw VarException(::format("{0} not specified", output->to_string()), {output});
        }
    }
    // the other way, this is to ensure a bijection
    for (auto const& iter : output_values_) {
        auto const& output = iter.first;
        if (outputs.find(output) == outputs.end()) {
            throw VarException(::format("{0} is not specified in FSM {1}", output->to_string(),
                                        parent_->fsm_name()),
                               {output});
        }
    }
}

}