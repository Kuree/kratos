#include "fault.hh"

#include <fstream>

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

void SimulationRun::add_simulation_coverage(const std::unordered_map<Stmt *, uint32_t> &coverage) {
    // for now we are not interested in stmt counts yet
    for (auto const &iter : coverage) {
        coverage_.emplace(iter.first);
    }
}

std::pair<Generator *, uint64_t> SimulationRun::select_gen(const std::vector<std::string> &tokens) {
    Generator *gen = top_;
    if (tokens[0] != gen->instance_name) return {nullptr, 1};
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
    } else if (stmt->type() == StatementType::FunctionalCall) {
        auto func = cast<FunctionCallStmt>(stmt);
        if (func->var()->func()->is_dpi()) {
            // nothing
        } else {
            compute_hit_stmts(state, result, func->var()->func());
        }
    } else {
        throw InternalException("Not implemented statement type");
    }
}

std::unordered_set<Stmt *> FaultAnalyzer::compute_coverage(uint32_t index) {
    auto run = runs_[index].get();
    std::unordered_set<Stmt *> result;
    if (run->has_coverage()) {
        auto const &cov = run->coverage();
        for (auto const &stmt: cov)
            result.emplace(stmt);
    } else {
        auto num_states = run->num_states();
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
    for (auto const &iter : wrong_stmt_count) {
        auto const &stmt = iter.first;
        if (correct_stmt_count.find(stmt) == correct_stmt_count.end()) result.emplace(stmt);
    }
    return result;
}

class CollectScopeStmtVisitor : public IRVisitor {
public:
    void visit(SequentialStmtBlock *stmt) override {
        // top level always get executed
        add_stmt_top(stmt);
    }

    void visit(CombinationalStmtBlock *stmt) override { add_stmt_top(stmt); }

    void visit(ScopedStmtBlock *stmt) override { add_stmt(stmt); }

    [[nodiscard]] const std::map<std::pair<std::string, uint32_t>, Stmt *> &stmt_map() const {
        return stmt_map_;
    }

    [[nodiscard]] const std::unordered_set<Stmt *> &top_stmts() const { return top_stmts_; }

private:
    void add_stmt(Stmt *stmt) {
        auto gen = stmt->generator_parent();
        if (!gen->verilog_fn.empty()) {
            stmt_map_.emplace(std::make_pair(gen->verilog_fn, stmt->verilog_ln), stmt);
        }
    }

    void add_stmt_top(Stmt *stmt) { top_stmts_.emplace(stmt); }

    std::map<std::pair<std::string, uint32_t>, Stmt *> stmt_map_;
    std::unordered_set<Stmt *> top_stmts_;
};

std::unordered_map<Stmt *, uint32_t> reverse_map_stmt(
    Generator *top, const std::set<std::tuple<std::string, uint32_t, uint32_t>> &hit_counts) {
    CollectScopeStmtVisitor visitor;
    visitor.visit_root(top);
    auto const &map = visitor.stmt_map();
    std::unordered_map<Stmt *, uint32_t> stmts;
    for (auto const &[fn, ln, count] : hit_counts) {
        if (count == 0) continue;
        // TODO implement basename in case verilator or the code gen uses full path
        auto entry = std::make_pair(fn, ln);
        if (map.find(entry) != map.end()) {
            stmts.emplace(map.at(entry), count);
        }
    }
    auto const &top_stmts = visitor.top_stmts();
    for (auto const &stmt: top_stmts) {
        // these block's calculation will be off, however,
        // it should not affect the outcome since all the runs will
        // run this part of logic
        stmts.emplace(stmt, 1);
    }
    return stmts;
}

std::unordered_map<Stmt*, uint32_t> compute_hit_stmts(const std::unordered_map<Stmt*, uint32_t> &stmts) {
    std::unordered_map<Stmt*, uint32_t> result;
    for (auto const &[stmt, count]: stmts) {
        if (stmt->type() == StatementType::Block) {
            auto block = cast<StmtBlock>(stmt);
            for (auto const &s: (*block)) {
                if (s->type() == StatementType::Assign) {
                    result.emplace(s.get(), count);
                }
            }
        }
    }

    return result;
}

std::unordered_map<Stmt *, uint32_t> parse_verilator_coverage(Generator *top,
                                                              const std::string &filename) {
    if (!fs::exists(filename))
        throw UserException(::format("{0} does not exist"));
    std::ifstream file(filename);
    std::set<std::tuple<std::string, uint32_t, uint32_t>> parse_result;
    for (std::string line; std::getline(file, line);) {
        if (line[0] != 'C') continue;
        // parse the line based on key value pair
        std::unordered_map<std::string, std::string> data;
        std::string key;
        std::string buffer;
        // a tiny FSM to decode
        // 0 -> nothing
        // 1 -> key
        // 2 -> value
        uint32_t state = 0;
        uint64_t index;
        for (index = 2; index < line.size(); index++) {
            auto c = line[index];
            if (state == 0) {
                if (c == 1) {
                    // this is key
                    state = 1;
                }
            } else if (state == 1) {
                if (c == 2) {
                    // key ends here
                    key = buffer;
                    buffer = "";
                    state = 2;
                } else {
                    buffer += c;
                }
            } else {
                if (c == '\'' || c == 1) {
                    // end of value
                    if (key.empty())
                        throw InternalException("Failed to parse" + line);
                    data.emplace(key, buffer);
                    key = "";
                    buffer = "";
                    if (c == 1) state = 1;
                    if (c == '\'') break;
                } else {
                    buffer += c;
                }
            }
        }
        // parse the page type
        if (data.find("page") == data.end())
            throw UserException("Unable to parse " + line);
        auto page_type = data.at("page");
        const std::string line_cov_prefix = "v_line";
        if (page_type.substr(0, line_cov_prefix.size()) != line_cov_prefix) continue;
        if (index >= line.size() - 1)
            throw UserException("Unable to parse " + line);
        // need to parse the count
        std::string count_s = line.substr(index + 1);
        string::trim(count_s);
        auto count = static_cast<uint64_t>(std::stol(count_s));
        // check on the filename and line number
        if (data.find("f") == data.end() || data.find("l") == data.end())
            throw UserException("Unable to parse" + line);
        auto const &fn = data.at("f");
        auto const ln = static_cast<uint32_t>(std::stoi(data.at("l")));
        parse_result.emplace(std::make_tuple(fn, ln, count));
    }

    auto reverse_map = reverse_map_stmt(top, parse_result);
    return compute_hit_stmts(reverse_map);
}

}  // namespace kratos
