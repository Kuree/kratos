#include "fault.hh"

#include "eval.hh"
#include "except.hh"
#include "fmt/format.h"
#include "graph.hh"
#include "stmt.hh"
#include "util.hh"

using fmt::format;

namespace kratos {

void SimulationRun::add_simulation_state(const std::map<std::string, int64_t> &values) {
    // need to parse the inputs and outputs
    states_.emplace_back(std::make_unique<Simulator>(top_));
    auto state = get_state(states_.size() - 1);
    for (auto const &[name, value] : values) {
        // we need to use dot notation to select from the hierarchy
        // notice these names do not contain the "top" name, e.g. TOP for verilator
        auto var = select(name);
        if (!var) {
            throw UserException(::format("Unable to parse {0}", name));
        }
        state->set(var, value, false);
    }
}

void SimulationRun::mark_wrong_value(const std::string &name) {
    if (states_.empty()) throw UserException("Simulation run is empty");
    auto v = select(name);
    auto v_base = const_cast<Var *>(v->get_var_root_parent());
    auto index = states_.size() - 1;
    wrong_value_[index].emplace(v_base);
}

std::pair<Generator *, uint64_t> SimulationRun::select_gen(const std::vector<std::string> &tokens) {
    Generator *gen = top_;
    if (tokens[0] != gen->instance_name)
        return {nullptr, 1};
    for (uint64_t index = 1; index < tokens.size(); index++) {
        auto const &name = tokens[index];
        if (!gen->has_child_generator(name)) {
            return {gen, index};
        } else {
            gen = gen->get_child_generator(name);
        }
    }
    return {gen, tokens.size()};
}

Var *SimulationRun::select(const std::string &name) {
    auto tokens = get_tokens(name, ".");
    auto [gen, index] = select_gen(tokens);
    if (index >= tokens.size()) return nullptr;
    if (!gen) return nullptr;
    auto var_tokens = std::vector<std::string>(tokens.begin() + index, tokens.end());
    // get var name, which has to be the first one
    auto const &var_name = var_tokens[0];
    auto var = gen->get_var(var_name).get();
    if (!var) return nullptr;

    if (var->is_packed()) {
        throw InternalException("Packed struct not supported yet");
    }
    // get index, if any
    std::vector<uint32_t> indices;
    for (uint64_t i = 1; i < var_tokens.size(); i++) {
        int v;
        try {
            v = std::stoi(var_tokens[i]);
        } catch (std::invalid_argument &) {
            return nullptr;
        }
        if (v < 0) throw UserException(::format("Unable to parse {0}", name));
        // slice it
        var = &(*var)[v];
    }
    return var;
}

Simulator *SimulationRun::get_state(uint32_t index) {
    if (index < states_.size()) {
        return states_[index].get();
    }
    return nullptr;
}

FaultAnalyzer::FaultAnalyzer(kratos::Generator *generator) : generator_(generator) {}

void FaultAnalyzer::add_simulation_run(const std::shared_ptr<SimulationRun> &run) {
    runs_.emplace_back(run);
}

template <typename T>
T *cast(Stmt *stmt) {
    auto r = dynamic_cast<T *>(stmt);
    if (!r) throw InternalException("Unable to cast stmt type");
    return r;
}

void compute_hit_stmts(Simulator *state, std::unordered_set<Stmt *> &result, Stmt *stmt) {
    if (stmt->type() == StatementType::If) {
        result.emplace(stmt);
        auto if_ = cast<IfStmt>(stmt);
        auto cond = if_->predicate();
        auto val = state->get(cond.get());
        if (val && *val) {
            compute_hit_stmts(state, result, if_->then_body().get());
        } else {
            compute_hit_stmts(state, result, if_->else_body().get());
        }
    } else if (stmt->type() == StatementType::Block) {
        auto block = cast<StmtBlock>(stmt);
        for (auto const &s : *block) {
            compute_hit_stmts(state, result, s.get());
        }
    } else if (stmt->type() == StatementType::Assign) {
        result.emplace(stmt);
    } else {
        throw InternalException("Not implemented statement type");
    }
}

std::unordered_set<Stmt *> FaultAnalyzer::compute_coverage(uint32_t index) {
    auto run = runs_[index].get();
    auto num_states = run->num_states();
    std::unordered_set<Stmt *> result;
    for (uint64_t i = 0; i < num_states; i++) {
        auto state = run->get_state(i);
        // given the state, we need to go through each generators
        GeneratorGraph g(generator_);
        auto generators = g.get_sorted_generators();
        for (auto const &gen : generators) {
            // need to calculate the sequential or combination block
            auto stmts = gen->get_all_stmts();
            for (auto const &stmt : stmts) {
                compute_hit_stmts(state, result, stmt.get());
            }
        }
    }
    coverage_maps_.emplace(index, result);
    return result;
}

std::unordered_set<Stmt *> FaultAnalyzer::compute_fault_stmts_from_coverage() {
    // compute coverage for each run
    auto const num_runs_ = num_runs();
    for (uint64_t i = 0; i < num_runs_; i++) {
        if (coverage_maps_.find(i) == coverage_maps_.end()) {
            compute_coverage(i);
        }
    }
    std::map<Stmt *, uint32_t> correct_stmt_count;
    std::map<Stmt *, uint32_t> wrong_stmt_count;
    for (auto const &[run_index, coverage] : coverage_maps_) {
        auto const &run = runs_[run_index];
        bool has_wrong_value = run->has_wrong_value();
        for (auto const &stmt : coverage) {
            if (has_wrong_value) {
                if (wrong_stmt_count.find(stmt) == wrong_stmt_count.end())
                    wrong_stmt_count[stmt] = 0;
                wrong_stmt_count[stmt] += 1;
            } else {
                if (correct_stmt_count.find(stmt) == correct_stmt_count.end())
                    correct_stmt_count[stmt] = 0;
                correct_stmt_count[stmt] += 1;
            }
        }
    }
    std::unordered_set<Stmt *> result;
    // compute the sum
    for (auto const &iter: wrong_stmt_count) {
        auto const &stmt = iter.first;
        if (correct_stmt_count.find(stmt) == correct_stmt_count.end())
            result.emplace(stmt);
    }
    return result;
}

}  // namespace kratos
