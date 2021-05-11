#include "fault.hh"

#include <chrono>
#include <fstream>
#include <stack>

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
    auto *state = get_state(states_.size() - 1);
    for (auto const &[name, value] : values) {
        // we need to use dot notation to select from the hierarchy
        // notice these names do not contain the "top" name, e.g. TOP for verilator
        auto *var = select(name);
        if (!var) {
            throw UserException(::format("Unable to parse {0}", name));
        }
        state->set(var, value, false);
    }
}

void SimulationRun::mark_wrong_value(const std::string &name) {
    if (states_.empty()) throw UserException("Simulation run is empty");
    auto *v = select(name);
    auto *v_base = const_cast<Var *>(v->get_var_root_parent());
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
    auto tokens = string::get_tokens(name, ".");
    auto [gen, index] = select_gen(tokens);
    if (index >= tokens.size()) return nullptr;
    if (!gen) return nullptr;
    auto var_tokens = std::vector<std::string>(tokens.begin() + index, tokens.end());
    // get var name, which has to be the first one
    auto const &var_name = var_tokens[0];
    auto *var = gen->get_var(var_name).get();
    if (!var) return nullptr;

    if (var->is_packed() && (var->size().size() > 1 || var->size()[0] > 1)) {
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
    auto *r = dynamic_cast<T *>(stmt);
    if (!r) throw InternalException("Unable to cast stmt type");
    return r;
}

void compute_hit_stmts(Simulator *state, std::unordered_set<Stmt *> &result, Stmt *stmt) {
    if (stmt->type() == StatementType::If) {
        auto *if_ = cast<IfStmt>(stmt);
        auto cond = if_->predicate();
        auto val = state->get(cond.get());
        if (val && *val) {
            compute_hit_stmts(state, result, if_->then_body().get());
        } else {
            compute_hit_stmts(state, result, if_->else_body().get());
        }
    } else if (stmt->type() == StatementType::Block) {
        auto *block = cast<StmtBlock>(stmt);
        // normal sequential block and combinational block always gets executed
        // as a result, we're only interested in the conditional statement block, i.e. scoped block
        if (block->block_type() == StatementBlockType::Scope) result.emplace(stmt);
        for (auto const &s : *block) {
            compute_hit_stmts(state, result, s.get());
        }
    } else if (stmt->type() == StatementType::FunctionalCall) {
        auto *func = cast<FunctionCallStmt>(stmt);
        if (func->var()->func()->is_dpi() || func->var()->func()->is_builtin()) {
            // nothing
        } else {
            compute_hit_stmts(state, result, func->var()->func());
        }
    }
}

std::unordered_set<Stmt *> FaultAnalyzer::compute_coverage(uint32_t index) {
    auto *run = runs_[index].get();
    std::unordered_set<Stmt *> result;
    if (run->has_coverage()) {
        auto const &cov = run->coverage();
        for (auto const &stmt : cov) result.emplace(stmt);
    } else {
        auto num_states = run->num_states();
        for (uint64_t i = 0; i < num_states; i++) {
            auto *state = run->get_state(i);
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

class XMLWriter {
    // code is adapted from
    // https://gist.github.com/sebclaeys/1227644/3761c33416d71c20efc300e78ea1dc36221185c5
public:
    XMLWriter(std::ostream &stream, const std::string &header) : stream_(stream) {
        stream_ << HEADER_;
        stream_ << header << std::endl;
    }

    XMLWriter &open_elt(const std::string &tag) {
        close_tag();
        if (!elt_stack_.empty()) stream_ << std::endl;
        indent();
        stream_ << "<" << tag;
        elt_stack_.emplace(tag);
        tag_open_ = true;
        new_line_ = false;
        return *this;
    }

    XMLWriter &close_elt() {
        close_tag();
        auto elt = elt_stack_.top();
        elt_stack_.pop();
        if (new_line_) {
            stream_ << std::endl;
            indent();
        }
        new_line_ = true;
        stream_ << "</" << elt << ">";
        return *this;
    }

    XMLWriter &close_all() {
        while (!elt_stack_.empty()) close_elt();
        return *this;
    }

    XMLWriter &attr(const std::string &key, const std::string &value) {
        stream_ << " " << key << "=\"";
        write_escape(value);
        stream_ << "\"";
        return *this;
    }

    template <class T>
    XMLWriter &attr(const std::string &key, T value) {
        return attr(key, ::format("{0}", value));
    }

    XMLWriter &content(const std::string &var) {
        close_tag();
        write_escape(var);
        return *this;
    }

private:
    std::ostream &stream_;
    bool tag_open_ = false;
    bool new_line_ = true;
    const std::string HEADER_ = "<?xml version=\"1.0\" encoding=\"utf-8\"?>\n";
    const std::string INDENT_ = "    ";
    std::stack<std::string> elt_stack_;

    inline void close_tag() {
        if (tag_open_) {
            stream_ << ">";
            tag_open_ = false;
        }
    }

    inline void indent() {
        for (uint64_t i = 0; i < elt_stack_.size(); i++) {
            stream_ << INDENT_;
        }
    }

    // not interested in this coverage
    // LCOV_EXCL_START
    inline void write_escape(const std::string &str) {
        // not interested in coverage for this function
        for (auto const &c : str) switch (c) {
                case '&':
                    stream_ << "&amp;";
                    break;
                case '<':
                    stream_ << "&lt;";
                    break;
                case '>':
                    stream_ << "&gt;";
                    break;
                case '\'':
                    stream_ << "&apos;";
                    break;
                case '"':
                    stream_ << "&quot;";
                    break;
                default:
                    stream_ << c;
                    break;
            }
    }
    // LCOV_EXCL_STOP
};

class CoverageStatVisitor : public IRVisitor {
public:
    void visit(AssignStmt *stmt) override {
        auto *parent = stmt->parent();
        if (parent->ir_node_kind() == IRNodeKind::StmtKind) {
            auto *st = reinterpret_cast<Stmt *>(parent);
            // we are only interested in
            if (st->type() == StatementType::Block) {
                auto *st_ = cast<StmtBlock>(st);
                if (st_->block_type() == StatementBlockType::Scope) {
                    // only add if it has coverage
                    if (!stmt->fn_name_ln.empty()) stmts_.emplace(stmt);
                }
            }
        }
    }

    void visit(ScopedStmtBlock *stmt) override {
        if (!stmt->fn_name_ln.empty()) branches_.emplace(stmt);
    }

    [[nodiscard]] const std::unordered_set<IRNode *> &stmts() const { return stmts_; }
    [[nodiscard]] const std::unordered_set<IRNode *> &branches() const { return branches_; }

private:
    std::unordered_set<IRNode *> stmts_;
    std::unordered_set<IRNode *> branches_;
};

IRNode *has_parent(const std::unordered_set<IRNode *> &parents, IRNode *stmt) {
    IRNode *node = stmt->parent();
    do {
        if (parents.find(node) != parents.end()) return node;
        node = node->parent();
    } while (node);
    return nullptr;
}

// adapted from
// https://www.rosettacode.org/wiki/Find_common_directory_path#C.2B.2B
std::string longestPath(const std::vector<std::string> &dirs, char separator) {
    if (dirs.empty()) return "";
    auto vsi = dirs.begin();
    int max_characters_common = static_cast<int>(vsi->length());
    std::string compare_string = *vsi;
    for (vsi = dirs.begin() + 1; vsi != dirs.end(); vsi++) {
        std::pair<std::string::const_iterator, std::string::const_iterator> p =
            std::mismatch(compare_string.begin(), compare_string.end(), vsi->begin());
        if ((p.first - compare_string.begin()) < max_characters_common)
            max_characters_common = p.first - compare_string.begin();
    }
    std::string::size_type found = compare_string.rfind(separator, max_characters_common);
    return compare_string.substr(0, found);
}

std::string get_filename_after_root(const std::string &root, const std::string &filename) {
    auto pos = filename.find(root) + root.size();
    auto sep = fs::separator();
    while (pos != std::string::npos && filename[pos] == sep) {
        pos++;
    }
    if (pos == std::string::npos) return filename;
    return filename.substr(pos);
}

void FaultAnalyzer::output_coverage_xml(const std::string &filename) {
    std::ofstream stream(filename, std::ofstream::trunc | std::ostream::out);
    output_coverage_xml(stream);
}

void FaultAnalyzer::output_coverage_xml(std::ostream &stream) {
    const std::string header =
        "<!DOCTYPE coverage SYSTEM "
        "'http://cobertura.sourceforge.net/xml/coverage-04.dtd'>";
    XMLWriter w(stream, header);

    // need to compute all the stats
    double line_total;
    double covered_line;
    double branch_total;
    double covered_branch;

    CoverageStatVisitor visitor;
    visitor.visit_root(generator_);

    auto const &total_branches = visitor.branches();
    branch_total = static_cast<double>(total_branches.size());
    auto const &total_lines = visitor.stmts();
    line_total = static_cast<double>(total_lines.size());

    // compute the collapsed map
    std::unordered_map<IRNode *, uint32_t> branch_cover_count;
    for (auto const &iter : coverage_maps_) {
        auto const &coverage = iter.second;
        for (auto const &stmt : coverage) {
            if (branch_cover_count.find(stmt) == branch_cover_count.end())
                branch_cover_count[stmt] = 0;
            branch_cover_count[stmt] += 1;
        }
    }

    // compute the actual coverage
    std::unordered_map<IRNode *, uint32_t> line_cover_count;
    for (auto *stmt : total_lines) {
        auto *parent = has_parent(total_branches, stmt);
        if (parent && branch_cover_count.find(parent) != branch_cover_count.end()) {
            auto count = branch_cover_count.at(parent);
            line_cover_count.emplace(stmt, count);
        }
    }

    covered_line = static_cast<double>(line_cover_count.size());
    covered_branch = static_cast<double>(branch_cover_count.size());

    // need to sort all the filename and lines
    std::map<std::string, std::map<uint32_t, IRNode *>> coverage;
    for (auto const &stmt : total_lines) {
        auto const &[fn, ln] = stmt->fn_name_ln.front();
        coverage[fn][ln] = stmt;
    }

    for (auto const &stmt : total_branches) {
        auto const &[fn, ln] = stmt->fn_name_ln.front();
        coverage[fn][ln] = stmt;
    }

    // find the root path
    // using the longest path
    std::vector<std::string> filenames;
    filenames.reserve(coverage.size());
    for (auto const &iter : coverage) filenames.emplace_back(iter.first);
    auto root = longestPath(filenames, fs::separator());

    // start to outputting the file coverage files
    auto now = std::chrono::system_clock::now();
    w.open_elt("coverage")
        .attr("line-rate", line_total > 0 ? covered_line / line_total : 0.0)
        .attr("branch-rate", branch_total > 0 ? covered_branch / branch_total : 0.0)
        .attr("lines-covered", static_cast<uint32_t>(covered_line))
        .attr("lines-valid", static_cast<uint32_t>(line_total))
        .attr("branches-covered", static_cast<uint32_t>(covered_branch))
        .attr("branches-valid", static_cast<uint32_t>(branch_total))
        .attr("complexity", 0.0)
        .attr("timestamp",
              std::chrono::duration_cast<std::chrono::seconds>(now.time_since_epoch()).count())
        .attr("version", ::format("kratos 0"));
    w.open_elt("sources").open_elt("source").content(root).close_elt().close_elt();

    // all the source files
    // packages
    w.open_elt("packages");
    w.open_elt("package");
    w.open_elt("classes");

    // FIXME: need to split path based to form the packages. for now only one package
    w.attr("line-rate", 1.0).attr("branch-rate", 1.0).attr("complexity", 1.0);
    for (auto const &[fn, stmts] : coverage) {
        // we need to group them by generator name
        std::map<std::string, std::map<uint32_t, IRNode *>> classes;
        for (auto const &[ln, stmt] : stmts) {
            auto *st = dynamic_cast<Stmt *>(stmt);
            if (!st) throw InternalException("Unable to cast stmt");
            auto gen_name = st->generator_parent()->name;
            classes[gen_name].emplace(ln, stmt);
        }

        auto new_fn = get_filename_after_root(root, fn);

        for (auto const &[class_name, cov] : classes) {
            w.open_elt("class");

            // TODO: add line rate and branch rate
            w.attr("name", class_name)
                .attr("filename", new_fn)
                .attr("line-rate", 1.0)
                .attr("branch-rate", 1.0)
                .attr("complexity", 1.0);
            // blank methods
            w.open_elt("methods").close_elt();
            w.open_elt("lines");

            for (auto const &[ln, stmt] : cov) {
                w.open_elt("line");

                // TODO add branch
                w.attr("number", ln);
                uint32_t count = 0;
                if (line_cover_count.find(stmt) != line_cover_count.end()) {
                    count = line_cover_count.at(stmt);
                } else if (branch_cover_count.find(stmt) != branch_cover_count.end()) {
                    count = branch_cover_count.at(stmt);
                }
                w.attr("hits", count);
                w.attr("branch", "false");
                w.close_elt();
            }

            w.close_elt();  // lines
            w.close_elt();  // class
        }
    }
    w.close_all();
}

class CollectScopeStmtVisitor : public IRVisitor {
public:
    void visit(ScopedStmtBlock *stmt) override { add_stmt(stmt); }

    [[nodiscard]] const std::map<std::pair<std::string, uint32_t>, Stmt *> &stmt_map() const {
        return stmt_map_;
    }

private:
    void add_stmt(Stmt *stmt) {
        auto *gen = stmt->generator_parent();
        if (!gen->verilog_fn.empty()) {
            auto filename = fs::basename(gen->verilog_fn);
            stmt_map_.emplace(std::make_pair(filename, stmt->verilog_ln), stmt);
        }
    }

    std::map<std::pair<std::string, uint32_t>, Stmt *> stmt_map_;
};

std::unordered_map<Stmt *, uint32_t> reverse_map_stmt(
    Generator *top, const std::set<std::tuple<std::string, uint32_t, uint32_t>> &hit_counts) {
    CollectScopeStmtVisitor visitor;
    visitor.visit_root(top);
    auto const &map = visitor.stmt_map();
    std::unordered_map<Stmt *, uint32_t> stmts;
    for (auto const &[fn, ln, count] : hit_counts) {
        if (count == 0) continue;
        auto filename = fs::basename(fn);
        auto entry = std::make_pair(filename, ln);
        if (map.find(entry) != map.end()) {
            stmts.emplace(map.at(entry), count);
        }
    }
    return stmts;
}

std::unordered_map<Stmt *, uint32_t> parse_verilator_coverage(Generator *top,
                                                              const std::string &filename) {
    if (!fs::exists(filename)) throw UserException(::format("{0} does not exist"));
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
                    if (key.empty()) throw InternalException("Failed to parse" + line);
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
        if (data.find("page") == data.end()) throw UserException("Unable to parse " + line);
        auto page_type = data.at("page");
        const std::string line_cov_prefix = "v_line";
        if (page_type.substr(0, line_cov_prefix.size()) != line_cov_prefix) continue;
        if (index >= line.size() - 1) throw UserException("Unable to parse " + line);
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
    return reverse_map;
}

std::vector<std::string> get_icc_tokens(std::string str) {
    std::vector<std::string> result;
    // trim the input and output
    string::trim(str);
    std::string buf;
    for (uint64_t pos = 0; pos < str.size(); pos++) {
        if (str[pos] == ' ') {
            if (pos < str.size() - 1) {
                if (str[pos + 1] == ' ') {
                    // end of token
                    string::trim(buf);
                    if (!buf.empty()) result.emplace_back(buf);
                    buf = "";
                    continue;
                }
            }
        }
        buf += str[pos];  // maybe more efficient way to do this?
    }

    if (!buf.empty()) result.emplace_back(buf);
    return result;
}

std::unordered_map<Stmt *, uint32_t> parse_icc_coverage(Generator *top,
                                                        const std::string &filename) {
    std::set<std::tuple<std::string, uint32_t, uint32_t>> parse_result;
    if (!fs::exists(filename)) throw UserException(::format("{0} does not exist"));
    std::ifstream file(filename);
    // state 0: nothing
    // state 1: searching for block header
    // state 2: reading block coverage
    uint32_t state = 0;
    uint32_t line_count = 0;
    std::string current_filename;
    for (std::string line; std::getline(file, line); line_count++) {
        // scan file by file
        string::trim(line);
        if (line[0] == '-') continue;  // skip the line section
        if (state == 0) {
            const std::string filename_tag = "File name:";
            auto pos = line.find(filename_tag);
            if (pos != std::string::npos) {
                state = 1;
                // extract out filename
                current_filename = line.substr(pos + filename_tag.size());
                string::trim(current_filename);
            }
        } else if (state == 1) {
            const std::string count_tag = "Count  Block";
            auto pos = line.find(count_tag);
            if (pos != std::string::npos) {
                state = 2;
            }
        } else {
            if (line.empty()) {
                // reset everything
                current_filename = "";
                state = 0;
                continue;
            }
            auto tokens = get_icc_tokens(line);
            if (tokens.size() < 6)
                throw UserException(::format("Unable to parse line {0} at file {1}:{2}", line,
                                             filename, line_count));
            auto count_s = tokens[0];
            auto line_num = tokens[2];
            // only takes the blocks if we are interested
            // since only the control statements determine what to run
            // we need to see if any of the branch has taken
            auto kind = tokens[3];
            const static std::unordered_set<std::string> allowed_branch_kind = {
                "true part of", "false part of", "a case item of"};
            if (allowed_branch_kind.find(kind) == allowed_branch_kind.end()) {
                // skip since it is just a normal code block
                continue;
            }

            auto count = static_cast<uint32_t>(std::stoi(count_s));
            auto fn = static_cast<uint32_t>(std::stoi(line_num));
            if (current_filename.empty())
                throw UserException(
                    ::format("Filename is empty, Unable to parse line {0} at file {1}:{2}", line,
                             filename, line_count));
            parse_result.emplace(std::make_tuple(current_filename, fn, count));
        }
    }
    auto reverse_map = reverse_map_stmt(top, parse_result);
    return reverse_map;
}

}  // namespace kratos
