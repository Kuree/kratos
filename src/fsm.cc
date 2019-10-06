#include "fsm.hh"
#include <fmt/format.h>
#include <cmath>
#include <fstream>
#include <queue>
#include <random>
#include <sstream>
#include <utility>
#include "except.hh"
#include "generator.hh"
#include "util.hh"

using fmt::format;
using std::endl;
using std::runtime_error;

namespace kratos {

std::map<FSMState*, color::Color> get_state_color(const std::vector<FSMState*>& states);

FSM::FSM(std::string name, kratos::Generator* generator)
    : fsm_name_(std::move(name)), generator_(generator) {
    // find the first clock signal
    auto vars = generator->get_ports(PortType::Clock);
    if (vars.empty()) {
        throw UserException("Unable to find any clock signal in " + generator->instance_name);
    }
    clk_ = generator_->get_port(vars[0]);
    // find the reset signal
    vars = generator->get_ports(PortType::AsyncReset);
    if (vars.empty()) {
        throw UserException("Unable to find any reset signal in " + generator->instance_name);
    }
    reset_ = generator_->get_port(vars[0]);
}

FSM::FSM(std::string name, kratos::Generator* generator, std::shared_ptr<Var> clk,
         std::shared_ptr<Var> reset)
    : fsm_name_(std::move(name)),
      generator_(generator),
      clk_(std::move(clk)),
      reset_(std::move(reset)) {}

void FSM::add_child_fsm(FSM* fsm) {
    if (fsm->generator_ != generator_)
        throw UserException(::format("FSM {0} doesn't have the same generator parent as {1}",
                                     fsm->fsm_name_, fsm_name_));
    child_fsms_.emplace(fsm->fsm_name_, fsm);
    fsm->parent_fsm_ = this;
    // erase the start from the child generator
    fsm->start_state_ = nullptr;
}

std::vector<FSMState*> FSM::get_all_child_states(bool include_extra_state) const {
    // this is a BFS search
    std::queue<FSMState*> queue;
    std::vector<FSMState*> result;
    std::unordered_set<FSMState*> visited;

    for (auto const& iter : states_) {
        queue.emplace(iter.second.get());
    }
    while (!queue.empty()) {
        auto state = queue.front();
        queue.pop();
        if (visited.find(state) != visited.end()) continue;
        visited.emplace(state);
        result.emplace_back(state);
        if (!state) continue;
        auto next_states = state->transitions();
        for (auto const& iter : next_states) {
            auto const next_state = iter.second;
            auto fsm = next_state->parent();
            while (fsm && fsm != this) {
                fsm = fsm->parent_fsm();
            }
            if (fsm == this) {
                queue.emplace(next_state);
            } else if (include_extra_state) {
                result.emplace_back(next_state);
            }
        }
    }
    return result;
}

void FSM::realize() {
    // generate the statements to the generator
    // first, get state and next state variable
    // compute number of states
    auto states = get_all_child_states(false);
    uint64_t num_states = states.size();
    if (!num_states) throw UserException(::format("FSM {0} is empty", fsm_name()));
    uint32_t width = std::ceil(std::log2(num_states));
    // define a enum type
    std::map<std::string, uint64_t> raw_def;
    uint64_t count = 0;
    if (!start_state_)
        throw UserException(::format("FSM {0} doesn't have a start state", fsm_name_));
    // name mapping
    std::unordered_map<FSMState*, std::string> state_name_mapping;
    bool has_child_state = !child_fsms_.empty();
    for (auto const& state : states) {
        // notice that we need to do an additional mapping if it's a nested fsm
        // to avoid any name conflicts
        std::string state_name;
        if (has_child_state) {
            state_name = state->parent()->fsm_name() + "_" + state->name();
        } else {
            state_name = state->name();
        }
        raw_def.emplace(state_name, count++);
        state_name_mapping.emplace(state, state_name);
        // check states
        state->check_outputs();
    }
    auto& enum_def = generator_->enum_(fsm_name_ + "_state", raw_def, width);
    // add debug info
    if (generator_->debug) {
        std::unordered_set<const FSM*> visited;
        for (auto const& state : states) {
            auto fsm = state->parent();
            if (visited.find(fsm) != visited.end()) continue;
            auto fn_ln = fsm->fn_name_ln_;
            for (auto const& [name, info] : fn_ln) {
                auto s = fsm->get_state(name).get();
                if (state_name_mapping.find(state) == state_name_mapping.end()) {
                    throw UserException(::format(
                        "Unable to find state name {0} from FSM {1}. Is it a disconnected state?",
                        s->name(), fsm_name_));
                }
                auto state_name = state_name_mapping.at(state);
                enum_def.add_debug_info(state_name, info);
            }
        }
    }
    // create two state variable, current_state, and next_state
    auto current_state_name = generator_->get_unique_variable_name(fsm_name_, "current_state");
    auto next_state_name = generator_->get_unique_variable_name(fsm_name_, "next_state");
    auto& current_state = generator_->enum_var(current_state_name, enum_def.shared_from_this());
    auto& next_state = generator_->enum_var(next_state_name, enum_def.shared_from_this());
    if (generator_->debug) {
        current_state.fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
        next_state.fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
    }

    // sequential logic
    // if (reset)
    //   current_state <= default_state
    // else
    //   current_state <= next_state
    auto seq = generator_->sequential();
    seq->add_condition({BlockEdgeType::Posedge, clk_});
    if (reset_->type() == VarType::PortIO &&
        (reset_->as<Port>()->active_high() && !(*reset_->as<Port>()->active_high())))
        seq->add_condition({BlockEdgeType::Negedge, reset_});
    else
        seq->add_condition({BlockEdgeType::Posedge, reset_});

    auto seq_if = std::make_shared<IfStmt>(reset_);
    {
        auto start_state_name = state_name_mapping.at(start_state_.get());
        auto stmt =
            current_state.assign(enum_def.get_enum(start_state_name), AssignmentType::NonBlocking);
        seq_if->add_then_stmt(stmt);
        if (generator_->debug) {
            if (!start_state_debug_.first.empty()) {
                stmt->fn_name_ln.emplace_back(start_state_debug_);
            }
            stmt->fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
        }
    }
    {
        auto stmt = current_state.assign(next_state.shared_from_this(), NonBlocking);
        if (generator_->debug) stmt->fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
        seq_if->add_else_stmt(stmt);
    }
    // add it to the seq
    seq->add_stmt(seq_if);

    // combination logic to compute next state
    generate_state_transition(enum_def, current_state, next_state, state_name_mapping);

    // now the output logic
    // only generate output state block in moore machine. in mealy machine, the output
    // is fused inside the state transition.
    if (moore_) generate_output(enum_def, current_state, state_name_mapping);

    // set to realized for all states
    auto fsms = get_all_child_fsm();
    for (auto& fsm : fsms) fsm->realized_ = true;
    realized_ = true;
}

std::shared_ptr<FunctionStmtBlock> FSM::get_func_def() {
    auto function_name = fsm_name_ + "_output";
    auto func = generator_->function(function_name);
    std::unordered_map<std::string, Var*> name_mapping;
    name_mapping.reserve(outputs_.size());
    // add outputs
    for (auto const& var : outputs_) {
        auto var_name = var->to_string() + "_value";
        func->input(var_name, var->width(), var->is_signed());
        name_mapping.emplace(var_name, var);
    }
    auto ports = func->ports();
    for (auto const& [var_name, port] : ports) {
        auto var = name_mapping.at(var_name);
        func->add_stmt(var->assign(port, AssignmentType::Blocking));
    }
    return func;
}

void add_debug_info(const FSMState* state, const std::shared_ptr<FunctionCallStmt>& func_stmt) {
    auto fn_ln = state->output_fn_ln();
    for (auto const& iter : fn_ln) {
        func_stmt->fn_name_ln.emplace_back(iter.second);
    }
}

void FSM::generate_state_transition(
    Enum& enum_def, EnumVar& current_state, EnumVar& next_state,
    const std::unordered_map<FSMState*, std::string>& state_name_mapping) {
    auto state_comb = generator_->combinational();
    std::shared_ptr<FunctionStmtBlock> func_def = nullptr;
    if (!moore_) func_def = get_func_def();
    auto case_state_comb = std::make_shared<SwitchStmt>(current_state.shared_from_this());
    auto states = get_all_child_states(false);
    for (auto const& state : states) {
        auto const& state_name = state_name_mapping.at(state);
        // a list of if statements
        std::shared_ptr<IfStmt> if_ = nullptr;
        std::shared_ptr<IfStmt> top_if = nullptr;
        std::vector<Var*> vars;
        auto transitions = state->transitions();
        vars.reserve(transitions.size());
        for (auto const& iter : transitions) vars.emplace_back(iter.first);
        // slide through condition
        bool has_slide_through = false;
        if (vars.size() != 1 || vars[0] != nullptr) {
            std::sort(vars.begin(), vars.end(), [=](const auto& lhs, const auto& rhs) {
                return transitions.at(lhs)->name() < transitions.at(rhs)->name();
            });
        } else {
            has_slide_through = true;
        }
        for (auto const& cond : vars) {
            auto next_fsm_state = transitions.at(cond);
            if (!cond) {
                // direct transition
                auto stmt = get_next_state_stmt(enum_def, next_state, state, next_fsm_state,
                                                state_name_mapping);
                case_state_comb->add_switch_case(enum_def.get_enum(state_name), stmt);
                break;
            }
            if (!if_) {
                if_ = std::make_shared<IfStmt>(cond->shared_from_this());
                auto stmt = get_next_state_stmt(enum_def, next_state, state, next_fsm_state,
                                                state_name_mapping);
                if_->add_then_stmt(stmt);
                // mealy machine need to add extra state transition outputs
                std::shared_ptr<FunctionCallStmt> func_stmt = nullptr;
                if (!moore_) {
                    get_func_call_stmt(func_def, next_fsm_state, func_stmt);
                    if_->add_then_stmt(func_stmt);
                }
                top_if = if_;
                if (generator_->debug) {
                    if (func_stmt) {
                        add_debug_info(state, func_stmt);
                        func_stmt->fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
                    }
                }
            } else {
                auto new_if = std::make_shared<IfStmt>(cond->shared_from_this());
                auto stmt = get_next_state_stmt(enum_def, next_state, state, next_fsm_state,
                                                state_name_mapping);
                // mealy machine need to add extra state transition outputs
                std::shared_ptr<FunctionCallStmt> func_stmt = nullptr;
                new_if->add_then_stmt(stmt);
                if (!moore_) {
                    get_func_call_stmt(func_def, next_fsm_state, func_stmt);
                    new_if->add_then_stmt(func_stmt);
                }
                if (generator_->debug) {
                    if (func_stmt) {
                        add_debug_info(state, func_stmt);
                        func_stmt->fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
                    }
                }
                if_->add_else_stmt(new_if);
                if_ = new_if;
            }
        }
        // prevent the reg being inferred as a latch
        // TODO: refactor this code
        if (if_) {
            auto stmt = get_next_state_stmt(enum_def, next_state, state, state, state_name_mapping);
            if_->add_else_stmt(stmt);
            // mealy machine need to add extra state transition outputs
            std::shared_ptr<FunctionCallStmt> func_stmt = nullptr;
            if (!moore_) {
                get_func_call_stmt(func_def, state, func_stmt);
                if_->add_else_stmt(func_stmt);
            }
            if (generator_->debug) {
                stmt->fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
                if (func_stmt) {
                    add_debug_info(state, func_stmt);
                    func_stmt->fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
                }
            }
        }

        if (!has_slide_through) {
            if (!top_if)
                throw InternalException(
                    ::format("Unable to find any state transition for state {0}", state->name()));
            case_state_comb->add_switch_case(enum_def.get_enum(state_name), top_if);
        }
    }
    // add it to the state_comb
    state_comb->add_stmt(case_state_comb);
}

std::shared_ptr<AssignStmt> FSM::get_next_state_stmt(
    Enum& enum_def, EnumVar& next_state, const FSMState* state, FSMState* next_fsm_state,
    const std::unordered_map<FSMState*, std::string>& state_name_mapping) const {
    auto const& next_fsm_state_name = state_name_mapping.at(next_fsm_state);
    auto stmt = next_state.assign(enum_def.get_enum(next_fsm_state_name), Blocking);
    auto debug_info = state->next_state_fn_ln();
    if (generator_->debug) {
        if (debug_info.find(next_fsm_state) != debug_info.end()) {
            auto info = debug_info.at(next_fsm_state);
            stmt->fn_name_ln.emplace_back(info);
        }
        stmt->fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
    }
    return stmt;
}
std::shared_ptr<FunctionCallStmt>& FSM::get_func_call_stmt(
    const std::shared_ptr<FunctionStmtBlock>& func_def, const FSMState* fsm_state,
    std::shared_ptr<FunctionCallStmt>& func_stmt) const {  // get arg mapping
    std::map<std::string, std::shared_ptr<Var>> mapping;
    auto const& output_values = fsm_state->output_values();
    for (auto const& [var_from, var_to] : output_values) {
        std::shared_ptr<Var> var_to_ =
            var_to ? var_to->shared_from_this() : var_from->shared_from_this();
        mapping.emplace(var_from->to_string() + "_value", var_to_);
    }
    func_stmt = std::make_shared<FunctionCallStmt>(func_def, mapping);
    return func_stmt;
}

void FSM::generate_output(Enum& enum_def, EnumVar& current_state,
                          const std::unordered_map<FSMState*, std::string>& state_name_mapping) {
    auto output_comb = generator_->combinational();
    auto output_case_comb = std::make_shared<SwitchStmt>(current_state.shared_from_this());
    auto states = get_all_child_states(false);
    for (auto const& state : states) {
        auto const& state_name = state_name_mapping.at(state);
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
            if (value && value != output_var) {
                // value can be a nullptr
                // users may use the same variable to indicate not changed
                auto stmt = output_var->assign(value->shared_from_this());
                if (generator_->debug) {
                    auto debug_info = state->output_fn_ln();
                    if (debug_info.find(output_var) != debug_info.end())
                        stmt->fn_name_ln.emplace_back(debug_info.at(output_var));
                }
                stmts.emplace_back(stmt);
            }
        }
        // add it to the case
        if (!stmts.empty()) {
            auto& case_stmt =
                output_case_comb->add_switch_case(enum_def.get_enum(state_name), stmts);
            generator_->add_named_block(::format("{0}_{1}_Output", fsm_name_, state_name),
                                        case_stmt.as<ScopedStmtBlock>());
        }
    }

    // add it to the output_comb
    output_comb->add_stmt(output_case_comb);
}

void FSM::output(const std::string& var_name) {
    auto var = generator_->get_var(var_name);
    output(var);
}

void FSM::output(const std::shared_ptr<Var>& var) {
    if (!var) throw UserException(::format("var not found in {0}", generator_->instance_name));
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
        throw UserException(::format("{0} already exists in the FSM", name));
    auto ptr = std::make_shared<FSMState>(name, this);
    states_.emplace(name, ptr);
    state_names_.emplace_back(name);
    return ptr;
}

std::shared_ptr<FSMState> FSM::add_state(const std::string& name,
                                         const std::pair<std::string, uint32_t>& debug_info) {
    // add debug info
    fn_name_ln_.emplace(name, debug_info);
    return add_state(name);
}

std::shared_ptr<FSMState> FSM::get_state(const std::string& name) const {
    if (states_.find(name) == states_.end())
        throw UserException(::format("Cannot find {0} in the FSM", name));
    return states_.at(name);
}

void FSM::set_start_state(const std::string& name) { set_start_state(get_state(name)); }

void FSM::set_start_state(const std::shared_ptr<FSMState>& state) { start_state_ = state; }

void FSM::set_start_state(const std::string& name, const std::pair<std::string, uint32_t>& debug) {
    set_start_state(name);
    start_state_debug_ = debug;
}

void FSM::set_start_state(const std::shared_ptr<FSMState>& state,
                          const std::pair<std::string, uint32_t>& debug) {
    set_start_state(state);
    start_state_debug_ = debug;
}

std::string FSM::dot_graph() {
    constexpr char indent[] = "    ";  // NOLINT
    std::stringstream stream;

    // header
    stream << "digraph " << fsm_name_ << " {" << endl;
    stream << indent << "rankdir=LR;" << ::endl << ::endl;

    // start state is double circle
    std::string start_state_name;
    if (start_state_) start_state_name = start_state_->handle_name();
    // we include extra states to draw the extra state transition diagram
    auto states = get_all_child_states(true);
    auto state_colors = get_state_color(states);
    if (!start_state_name.empty()) {
        auto color = state_colors.at(start_state_.get());
        auto color_str = ::format("#{0:02X}{1:02X}{2:02X}", color.R, color.G, color.B);
        stream
            << indent
            << ::format(
                   R"(node [shape=doublecircle, label="{0}", style=filled, fillcolor="{1}"] {0};)",
                   start_state_->handle_name(), color_str)
            << ::endl;
    }
    // the rest of the states
    for (auto const& iter : states) {
        auto state_name = iter->handle_name();
        if (state_name == start_state_name) continue;
        auto color = state_colors.at(iter);
        auto color_str = ::format("#{0:02X}{1:02X}{2:02X}", color.R, color.G, color.B);
        stream << indent
               << ::format(
                      R"(node [shape=circle, label="{0}", style=filled, fillcolor="{1}"] {0};)",
                      state_name, color_str)
               << ::endl;
    }

    stream << ::endl;
    // state transition
    for (auto const& state : states) {
        auto transitions = state->transitions();
        auto state_name = state->handle_name();
        // deterministic sorting
        std::vector<Var*> conds;
        conds.reserve(transitions.size());
        for (auto const& iter : transitions) conds.emplace_back(iter.first);
        std::sort(conds.begin(), conds.end(), [](auto const& lhs, auto const& rhs) {
            return lhs->to_string() < rhs->to_string();
        });
        for (auto const& cond : conds) {
            auto next_state = transitions.at(cond);
            if (cond) {
                stream << indent
                       << ::format("{0}    ->  {1} [ label = \"{2}\" ];", state_name,
                                   next_state->handle_name(), cond->to_string())
                       << ::endl;
            } else {
                stream << indent
                       << ::format("{0}    ->  {1};", state_name, next_state->handle_name())
                       << ::endl;
            }
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

std::vector<FSM*> FSM::get_all_child_fsm() const {
    std::vector<FSM*> result;
    std::queue<FSM*> queue;
    std::unordered_set<const FSM*> visited;
    queue.emplace(const_cast<FSM*>(this));
    while (!queue.empty()) {
        auto fsm = queue.front();
        queue.pop();
        result.emplace_back(fsm);
        if (visited.find(fsm) != visited.end())
            throw UserException(::format("FSM {0} has circular dependency", fsm_name_));

        visited.emplace(fsm);
        auto children = fsm->child_fsms_;
        for (auto const& iter : children) queue.emplace(iter.second);
    }
    return result;
}

std::map<FSMState*, color::Color> get_state_color(const std::vector<FSMState*>& states) {
    std::map<FSMState*, color::Color> result = {};
    std::map<const FSM*, color::Color> state_color;
    // set seed to 0
    std::mt19937 gen(1);  // NOLINT
    std::uniform_real_distribution<double> dis(0, 1.0);
    for (auto const& state : states) {
        auto fsm = state->parent();
        if (state_color.find(fsm) == state_color.end()) {
            // get a new color
            double h = dis(gen);
            // use golden ratio
            // https://martin.ankerl.com/2009/12/09/how-to-create-random-colors-programmatically/
            h += 0.618033988749895;
            h = std::fmod(h, 1.0);
            auto color = color::hsv_to_rgb(h, 0.5, 0.95);
            state_color.emplace(fsm, color);
        }
    }

    // second pass the assign colors
    for (auto& state : states) {
        auto fsm = state->parent();
        result.emplace(state, state_color.at(fsm));
    }

    return result;
}

FSMState::FSMState(std::string name, FSM* parent) : name_(std::move(name)), parent_(parent) {}

void FSMState::next(const std::shared_ptr<FSMState>& next_state, const std::shared_ptr<Var>& cond) {
    if (!next_state || !next_state->parent_)
        throw UserException(
            ::format("Next state for {0}.{1} cannot be null", parent_->fsm_name(), name_));
    // making sure that it's part of the same fsm state
    auto parent = parent_;
    auto state_ptr = next_state.get();
    while (parent->parent_fsm()) parent = parent->parent_fsm();
    auto fsm = next_state->parent_;
    while (fsm && fsm != parent) {
        fsm = fsm->parent_fsm();
    }
    if (fsm != parent) {
        throw UserException(::format("FSM state {0} belongs to a different FSM {1} than {2}",
                                     next_state->name_, next_state->parent_->fsm_name(),
                                     parent->fsm_name()));
    }

    if (!cond) {
        transitions_.emplace(nullptr, state_ptr);
    } else {
        if (transitions_.find(nullptr) != transitions_.end()) {
            // we have a slide through
            throw UserException("Unconditional transition has been assign to " + name_);
        }
        auto ptr = cond.get();
        if (cond->width() != 1) throw VarException("Condition has to be a boolean value", {ptr});

        if (transitions_.find(ptr) != transitions_.end()) {
            throw ::runtime_error(::format("{0} has been added to FSM {1}-{2} already",
                                           ptr->to_string(), parent_->fsm_name(), name_));
        }
        transitions_.emplace(ptr, state_ptr);
    }
}

void FSMState::next(const std::shared_ptr<FSMState>& next_state, const std::shared_ptr<Var>& cond,
                    const std::pair<std::string, uint32_t>& debug_info) {
    next(next_state, cond);
    next_state_fn_ln_.emplace(next_state.get(), debug_info);
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
    auto& c = constant(value, output_var->width(), output_var->is_signed());
    output(output_var, c.shared_from_this());
}

void FSMState::output(const std::shared_ptr<Var>& output_var, int64_t value,
                      const std::pair<std::string, uint32_t>& debug_info) {
    output_fn_ln_.emplace(output_var.get(), debug_info);
    output(output_var, value);
}

void FSMState::output(const std::shared_ptr<Var>& output_var, const std::shared_ptr<Var>& value_var,
                      const std::pair<std::string, uint32_t>& debug_info) {
    output_fn_ln_.emplace(output_var.get(), debug_info);
    output(output_var, value_var);
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

std::string FSMState::handle_name() const {
    auto str = name_;
    auto current = parent_;
    auto p = parent_->parent_fsm();
    while (p) {
        str = ::format("{0}_{1}", current->fsm_name(), str);
        current = p;
        p = p->parent_fsm();
    }
    return str;
}

}  // namespace kratos
