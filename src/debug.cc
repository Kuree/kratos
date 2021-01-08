#include "debug.hh"

#include <mutex>

#include "except.hh"
#include "fmt/format.h"
#include "generator.hh"
#include "graph.hh"
#include "pass.hh"
#include "schema.hh"
#include "tb.hh"
#include "util.hh"

using fmt::format;

namespace kratos {

class DebugBreakInjectVisitor : public IRVisitor {
public:
    explicit DebugBreakInjectVisitor(Context *context) : context_(context) {}

    void visit(CombinationalStmtBlock *stmt) override { insert_statements(stmt); }

    void visit(SequentialStmtBlock *stmt) override { insert_statements(stmt); }

    void visit(InitialStmtBlock *stmt) override { insert_statements(stmt); }

    void visit(ScopedStmtBlock *stmt) override { insert_statements(stmt); }

    void visit(AssignStmt *stmt) override {
        auto const *parent = stmt->parent();
        if (parent->ir_node_kind() == IRNodeKind::GeneratorKind) {
            auto const *p = reinterpret_cast<const Generator *>(parent);
            if (p->debug) {
                process_stmt(stmt);
            }
        }
    }

private:
    void insert_statements(StmtBlock *block) {
        auto *parent = block->generator_parent();
        if (!parent->debug)
            // we only insert statements to the ones that has debug turned on
            return;

        for (auto const &stmt : *block) {
            process_stmt(stmt.get());
        }
    }

    void process_stmt(Stmt *stmt) {
        uint32_t stmt_id = context_->max_stmt_id()++;
        // set stmt id
        stmt->set_stmt_id(stmt_id);
    }

    Context *context_;
};

void inject_debug_break_points(Generator *top) {
    DebugBreakInjectVisitor visitor(top->context());
    visitor.visit_root(top);
}

class InstanceIdVisitor : public IRVisitor {
public:
    explicit InstanceIdVisitor(Context *context) : context_(context) {}

    void visit(Generator *gen) override {
        if (gen->generator_id < 0) {
            mutex_.lock();
            auto id = context_->max_instance_id()++;
            mutex_.unlock();
            gen->generator_id = id;
            // create a parameter
            auto &p = gen->parameter(break_point_param_name, 32);
            p.set_value(id);
        }
    }

private:
    Context *context_;
    std::mutex mutex_;
};

void inject_instance_ids(Generator *top) {
    // this can be done in parallel
    InstanceIdVisitor visitor(top->context());
    visitor.visit_generator_root_p(top);
}

class ExtractDebugVisitor : public IRVisitor {
public:
    void visit(AssignStmt *stmt) override { extract_stmt_id(stmt); }
    void visit(ScopedStmtBlock *stmt) override { extract_stmt_id(stmt); }
    void visit(IfStmt *stmt) override { extract_stmt_id(stmt); }
    void visit(SwitchStmt *stmt) override { extract_stmt_id(stmt); }
    void visit(FunctionCallStmt *stmt) override { extract_stmt_id(stmt); }
    void visit(ReturnStmt *stmt) override { extract_stmt_id(stmt); }
    void visit(AssertBase *stmt) override { extract_stmt_id(stmt); }

    const std::map<Stmt *, uint32_t> &map() const { return map_; }

private:
    void extract_stmt_id(Stmt *stmt) {
        int id = stmt->stmt_id();
        if (id >= 0) {
            map_.emplace(stmt, id);
        }
    }

    std::map<Stmt *, uint32_t> map_;
};

std::map<Stmt *, uint32_t> extract_debug_break_points(Generator *top) {
    ExtractDebugVisitor visitor;
    visitor.visit_root(top);
    return visitor.map();
}

class InsertVerilatorPublic : public IRVisitor {
public:
    void visit(Generator *generator) override {
        auto vars = generator->get_all_var_names();
        for (auto const &var_name : vars) {
            auto var = generator->get_var(var_name);
            insert_str(var.get());
        }
    }

private:
    void static insert_str(Var *var) { var->set_after_var_str_(" /*verilator public*/"); }
};

void insert_verilator_public(Generator *top) {
    InsertVerilatorPublic visitor;
    visitor.visit_generator_root_p(top);
}

class VarSourceVisitor : public IRVisitor {
public:
    void visit(Var *var) override {
        if (map_.find(var) != map_.end()) return;
        auto const &sources = var->sources();
        for (auto const &stmt : sources) {
            auto *right = stmt->right();
            get_source_var(right, map_[var]);
        }
    }

    const std::unordered_map<Var *, std::unordered_set<Var *>> &map() const { return map_; }

private:
    std::unordered_map<Var *, std::unordered_set<Var *>> map_;

    class VarComponentVisitor : public IRVisitor {
    public:
        std::unordered_set<Var *> &vars() { return vars_; };
        void visit(Var *var) override {
            if (var->type() == VarType::Base) {
                vars_.emplace(var);
            }
        }

    private:
        std::unordered_set<Var *> vars_;
    };

    void static get_source_var(const Var *var, std::unordered_set<Var *> &set) {
        if (var->type() == VarType::ConstValue || var->type() == VarType::Parameter) return;
        VarComponentVisitor visitor;
        visitor.visit_root(const_cast<Var *>(var));
        set.merge(visitor.vars());
    }
};

std::unordered_map<Var *, std::unordered_set<Var *>> find_driver_signal(Generator *top) {
    VarSourceVisitor visitor;
    visitor.visit_root(top);
    return visitor.map();
}

class PropagateScopeVisitor : public IRVisitor {
public:
    void visit(IfStmt *stmt) override {
        auto variables = stmt->scope_context();
        for (auto const &[name, var] : variables) {
            stmt->then_body()->add_scope_variable(name, var.second, var.first, false);
            stmt->else_body()->add_scope_variable(name, var.second, var.first, false);
        }
    }

    void visit(SwitchStmt *stmt) override {
        auto variables = stmt->scope_context();
        for (auto const &[name, var] : variables) {
            auto cases = stmt->body();
            for (auto &iter : cases) {
                auto case_ = iter.second;
                case_->add_scope_variable(name, var.second, var.first, false);
            }
        }
    }
};

void propagate_scope_variable(Generator *top) {
    PropagateScopeVisitor visitor;
    visitor.visit_root(top);
}

void mock_hierarchy(Generator *top, const std::string &top_name) {
    // can only perform on the top layer
    auto instance_name = top->instance_name;
    if (instance_name.find('.') == std::string::npos) {
        return;
    }
    // need to tokenize based on the instance names
    auto names = string::get_tokens(instance_name, ".");
    if (names.size() < 2) throw InternalException("Cannot tokenize string " + instance_name);
    Context *context = top->context();
    top->instance_name = names.back();
    int start_index = static_cast<int>(names.size() - 2);
    Generator *pre = top;
    for (int i = start_index; i >= 0; i--) {
        // create a new generator
        std::string name = names[i];
        if (i == 0 && !top_name.empty()) name = top_name;
        Generator *gen;
        if (context->generator_name_exists(name)) {
            gen = (*(context->get_generators_by_name(name).begin())).get();
        } else {
            gen = &context->generator(name);
        }
        gen->add_child_generator(pre->instance_name, pre->shared_from_this());
        pre = gen;
    }
}

void DebugDatabase::compute_generators(Generator *top) {
    top_ = top;
    GeneratorGraph g(top);
    auto generators = g.get_sorted_generators();
    for (auto *gen : generators) {
        generators_.emplace(gen);
    }
}

void DebugDatabase::set_break_points(Generator *top) { set_break_points(top, ".py"); }

void DebugDatabase::set_break_points(Generator *top, const std::string &ext) {
    // set the break points
    break_points_ = extract_debug_break_points(top);

    // index all the front-end code
    // we are only interested in the files that has the extension
    for (auto const &[stmt, id] : break_points_) {
        auto fn_ln = stmt->fn_name_ln;
        for (auto const &[fn, ln] : fn_ln) {
            auto fn_ext = fs::get_ext(fn);
            if (fn_ext == ext) {
                // this is the one we need
                stmt_mapping_.emplace(stmt, std::make_pair(fn, ln));
                auto *gen = stmt->generator_parent();
                generator_break_points_[gen].emplace(id);
                break;
            }
        }
    }
    // set generators
    compute_generators(top);
}

void DebugDatabase::set_variable_mapping(
    const std::map<Generator *, std::map<std::string, Var *>> &mapping) {
    for (auto const &[gen, map] : mapping) {
        auto handle_name = gen->handle_name();

        variable_mapping_.emplace(handle_name,
                                  std::make_pair(gen, std::map<std::string, std::string>()));

        for (auto const &[front_var_name, var] : map) {
            variable_mapping_[handle_name].second.emplace(front_var_name, var->to_string());
        }
    }
}

void DebugDatabase::set_variable_mapping(
    const std::map<Generator *, std::map<std::string, std::string>> &mapping) {
    for (auto const &[gen, map] : mapping) {
        auto handle_name = gen->handle_name();

        variable_mapping_.emplace(handle_name,
                                  std::make_pair(gen, std::map<std::string, std::string>()));

        for (auto const &[front_var_name, var_name] : map) {
            variable_mapping_[handle_name].second.emplace(front_var_name, var_name);
        }
    }
}

class StmtContextVisitor : public IRVisitor {
public:
    void visit(IfStmt *stmt) override { add_content(stmt); }

    void visit(AssignStmt *stmt) override { add_content(stmt); }

    const std::map<Stmt *, std::map<std::string, std::pair<bool, std::string>>> &stmt_context()
        const {
        return stmt_context_;
    }

private:
    void add_content(Stmt *stmt) {
        if (!stmt->scope_context().empty()) {
            stmt_context_.emplace(stmt, stmt->scope_context());
        }
    }
    std::map<Stmt *, std::map<std::string, std::pair<bool, std::string>>> stmt_context_;
};

void DebugDatabase::set_stmt_context(kratos::Generator *top) {
    StmtContextVisitor visitor;
    visitor.visit_root(top);
    stmt_context_ = visitor.stmt_context();
}

void DebugDatabase::save_database(const std::string &filename, bool override) {
    if (override) {
        if (fs::exists(filename)) {
            fs::remove(filename);
        }
    }
    auto storage = hgdb::init_debug_db(filename);
    storage.sync_schema();

    // compute breakpoint conditions
    auto breakpoint_conditions = compute_enable_condition(top_);
    // insert tables

    // insert generator ids
    std::unordered_map<const Generator *, uint32_t> gen_id_map;
    std::unordered_map<std::string, uint32_t> handle_id_map;
    for (auto const &gen : generators_) {
        if (gen->generator_id < 0) {
            // assign a new ID
            gen->generator_id = gen->context()->max_instance_id()++;
        }
        int id = gen->generator_id;
        gen_id_map.emplace(gen, id);
        handle_id_map.emplace(gen->handle_name(), id);
        hgdb::store_instance(storage, gen->generator_id, gen->handle_name());
    }

    // break points
    for (auto const &[stmt, id] : break_points_) {
        if (stmt_mapping_.find(stmt) != stmt_mapping_.end()) {
            auto const &[fn, ln] = stmt_mapping_.at(stmt);
            auto const *gen = stmt->generator_parent();
            auto instance_id = gen_id_map.at(gen);
            std::string condition;
            if (breakpoint_conditions.find(stmt) != breakpoint_conditions.end())
                condition = breakpoint_conditions.at(stmt);
            // we don't support column breakpoint since there is normally no such usage in
            // Python
            hgdb::store_breakpoint(storage, id, instance_id, fn, ln, 0, condition);
        }
    }

    // variables
    int variable_count = 0;
    std::unordered_set<Var *> var_id_set;
    std::map<std::tuple<const int, std::string, std::string>, int> var_id_mapping;
    std::unordered_map<Generator *, std::map<std::string, std::string>> self_context_mapping;
    // function to create variable and flatten the hierarchy
    // NOLINTNEXTLINE
    auto create_variable = [&](Var *var_, const int handle_id_, const std::string &name_,
                               const std::string &value_, bool is_context_, uint32_t breakpoint_id_,
                               bool gen_var = false) {
        hgdb::Variable v;
        v.is_rtl = var_ != nullptr;
        auto hierarchy_name = var_? ::format("{0}.", var_->generator()->instance_name): "";

        auto add_context_gen = [&](const std::string &name) {
            if (is_context_) {
                // create context mapping as well
                hgdb::store_context_variable(storage, name, breakpoint_id_, v.id);
            }
            if (gen_var) {
                hgdb::store_generator_variable(storage, name, handle_id_, v.id);
            }
        };

        if (var_) {
            // it is an variable
            if (var_->size().size() > 1 || var_->size().front() > 1) {
                // it's an array. need to flatten it
                auto slices = get_flatten_slices(var_);
                for (auto const &slice : slices) {
                    std::string new_name = name_;
                    for (auto const &s : slice) new_name = ::format("{0}.{1}", new_name, s);
                    std::string value = var_->name;
                    for (auto const &s : slice) value = ::format("{0}[{1}]", value, s);
                    v.value = value;
                    if (var_id_mapping.find(std::make_tuple(handle_id_, new_name, v.value)) ==
                        var_id_mapping.end()) {
                        v.id = variable_count++;
                        hgdb::store_variable(storage, v.id, hierarchy_name + v.value);
                        var_id_mapping.emplace(
                            std::make_pair(std::make_tuple(handle_id_, new_name, v.value), v.id));
                    } else {
                        v.id = var_id_mapping.at(std::make_tuple(handle_id_, new_name, v.value));
                    }
                    add_context_gen(new_name);
                }
            } else if (var_->is_struct()) {
                // it's an packed array
                if (var_->type() == VarType::PortIO) {
                    auto *p = reinterpret_cast<PortPackedStruct *>(var_);
                    auto const &def = p->packed_struct();
                    for (auto const &iter : def.attributes) {
                        auto const &attr_name = std::get<0>(iter);
                        // we need to store lots of them
                        std::string new_name = ::format("{0}.{1}", name_, attr_name);
                        v.value = ::format("{0}.{1}", var_->name, attr_name);
                        if (var_id_mapping.find(std::make_tuple(handle_id_, new_name, v.value)) ==
                            var_id_mapping.end()) {
                            v.id = variable_count++;
                            hgdb::store_variable(storage, v.id, hierarchy_name + v.value);
                            var_id_mapping.emplace(std::make_pair(
                                std::make_tuple(handle_id_, new_name, v.value), v.id));
                        } else {
                            v.id =
                                var_id_mapping.at(std::make_tuple(handle_id_, new_name, v.value));
                        }
                        add_context_gen(new_name);
                    }
                } else if (var_->type() == VarType::Base) {
                    auto *p = reinterpret_cast<VarPackedStruct *>(var_);
                    auto const &def = p->packed_struct();
                    for (auto const &iter : def.attributes) {
                        auto const &attr_name = std::get<0>(iter);
                        // we need to store lots of them
                        std::string new_name = ::format("{0}.{1}", name_, attr_name);
                        v.value = ::format("{0}.{1}", var_->name, attr_name);
                        if (var_id_mapping.find(std::make_tuple(handle_id_, new_name, v.value)) ==
                            var_id_mapping.end()) {
                            v.id = variable_count++;
                            hgdb::store_variable(storage, v.id, hierarchy_name + v.value);
                            var_id_mapping.emplace(std::make_pair(
                                std::make_tuple(handle_id_, new_name, v.value), v.id));
                        } else {
                            v.id =
                                var_id_mapping.at(std::make_tuple(handle_id_, new_name, v.value));
                        }
                        add_context_gen(new_name);
                    }
                }
            } else {
                // the normal one
                v.value = var_->name;
                if (var_id_mapping.find(std::make_tuple(handle_id_, name_, v.value)) ==
                    var_id_mapping.end()) {
                    v.id = variable_count++;
                    hgdb::store_variable(storage, v.id, hierarchy_name + v.value);
                    var_id_mapping.emplace(
                        std::make_pair(std::make_tuple(handle_id_, name_, v.value), v.id));
                } else {
                    v.id = var_id_mapping.at(std::make_tuple(handle_id_, name_, v.value));
                }
                add_context_gen(name_);
            }
            var_id_set.emplace(var_);
        } else {
            // directly store it
            if (name_.empty()) {
                throw UserException(::format("Non-variable cannot have empty name in database"));
            }
            v.value = value_;
            v.id = variable_count++;
            hgdb::store_variable(storage, v.id, v.value, false);
            add_context_gen(name_);
        }
    };
    for (auto const &[handle_name, gen_map] : variable_mapping_) {
        auto const &[gen, vars] = gen_map;
        if (gen_id_map.find(gen) == gen_id_map.end())
            throw InternalException(::format("Unable to find generator {0}", gen->handle_name()));
        self_context_mapping.emplace(gen, vars);
        auto id = gen_id_map.at(gen);
        // this will be generator instance values (RTL correspondence)
        auto all_vars = gen->get_all_var_names();
        for (auto const &var_name : all_vars) {
            auto var = gen->get_var(var_name);
            if (var && (var->type() == VarType::Base || var->type() == VarType::PortIO)) {
                create_variable(var.get(), id, var_name, var_name, false, 0, true);
            }
        }
    }

    // local context variables
    for (auto const &[stmt, id] : break_points_) {
        // use breakpoint as an index since we can only get context as we hit potential breakpoints
        auto const &gen = stmt->generator_parent();
        auto handle_name = gen->handle_name();
        if (stmt_context_.find(stmt) == stmt_context_.end()) continue;
        if (stmt_mapping_.find(stmt) == stmt_mapping_.end()) continue;
        if (handle_id_map.find(handle_name) == handle_id_map.end())
            throw InternalException(::format("Unable to find {0} in handle id map", handle_name));

        auto const &self_vars = self_context_mapping.at(gen);
        auto instance_id = handle_id_map.at(handle_name);
        auto values = stmt_context_.at(stmt);

        for (auto const &[key, entry] : values) {
            auto const &[is_var, value] = entry;
            auto *gen_var = is_var ? gen->get_var(value).get() : nullptr;
            create_variable(gen_var, instance_id, key, value, true, id);
        }

        // self/this instance
        for (auto const &[front_var, var] : self_vars) {
            Var *gen_var = gen->get_var(var).get();
            if (!gen_var) {
                gen_var = gen->get_param(var).get();
            }
            if (!gen_var) {
                create_variable(nullptr, instance_id, front_var, var, true, id);
            } else {
                create_variable(gen_var, instance_id, front_var, var, true, id);
            }
        }
    }
}

void inject_clock_break_points(Generator *top) {
    // trying to find the clock automatically
    auto const &port_names = top->get_port_names();
    for (auto const &port_name : port_names) {
        auto const &port = top->get_port(port_name);
        if (port && port->port_type() == PortType::Clock) {
            inject_clock_break_points(top, port);
            return;
        }
    }
    // don't do anything
}
void inject_clock_break_points(Generator *top, const std::string &clk_name) {
    auto port = top->get_port(clk_name);
    if (port) {
        inject_clock_break_points(top, port);
    } else {
        throw UserException(::format("{0} is not a clock port", clk_name));
    }
}
void inject_clock_break_points(Generator *top, const std::shared_ptr<Port> &port) {
    if (!port) {
        // find the clock
        inject_clock_break_points(top);
    } else {
        // we use negative edge to jump to clock because most of the designs are
        // on posedge
        auto seq = top->sequential();
        seq->add_condition({BlockEdgeType::Negedge, port});
        // inject a breakpoint_clock call
        // create the function in the generator
        top->dpi_function(break_point_clock_func_name);
        auto &var = top->call(break_point_clock_func_name, {}, false);
        auto stmt = std::make_shared<FunctionCallStmt>(var.as<FunctionCallVar>());
        seq->add_stmt(stmt);
    }
}

class AssertVisitor : public IRVisitor {
public:
    void visit(AssertBase *base) override {
        if (base->assert_type() == AssertType::AssertValue) {
            auto *stmt = reinterpret_cast<AssertValueStmt *>(base);
            // create a function call
            auto *gen = base->generator_parent();
            if (!gen->has_function(exception_func_name)) {
                auto func = gen->dpi_function(exception_func_name);
                func->input(break_point_instance_id_arg, var_size_, false);
                func->input(var_name_, var_size_, false);
                func->set_port_ordering({{break_point_instance_id_arg, 0}, {var_name_, 1}});
            }
            // get the stmt from the assert
            auto id = stmt->stmt_id();
            auto &id_const = constant(id, var_size_);
            auto instance_id = gen->get_param(break_point_param_name);
            if (!instance_id) {
                throw UserException("Cannot find " + std::string(break_point_param_name));
            }
            auto &var = gen->call(exception_func_name,
                                  {{break_point_instance_id_arg, instance_id},
                                   {var_name_, id_const.shared_from_this()}},
                                  false);
            auto st = std::make_shared<FunctionCallStmt>(var.as<FunctionCallVar>());
            stmt->set_else(st);
        }
    }

private:
    const std::string var_name_ = break_point_func_arg;
    const uint32_t var_size_ = 32;
};

void inject_assert_fail_exception(Generator *top) {
    AssertVisitor visitor;
    visitor.visit_root(top);
}

// TODO: implement transformer visitor
class AssertionRemoval : public IRVisitor {
public:
    void visit(Generator *gen) override {
        auto stmt_count = gen->stmts_count();
        std::vector<std::shared_ptr<Stmt>> stmts_to_remove;
        for (uint64_t i = 0; i < stmt_count; i++) {
            auto stmt = gen->get_stmt(i);
            if (stmt->type() == StatementType::Assert) stmts_to_remove.emplace_back(stmt);
        }
        for (auto const &stmt : stmts_to_remove) {
            gen->remove_stmt(stmt);
        }
    }

    void visit(ScopedStmtBlock *block) override { process_block(block); }
    void visit(SequentialStmtBlock *block) override { process_block(block); }
    void visit(CombinationalStmtBlock *block) override { process_block(block); }

    static void process_block(StmtBlock *block) {
        auto stmt_count = block->child_count();
        std::vector<std::shared_ptr<Stmt>> stmts_to_remove;
        for (uint64_t i = 0; i < stmt_count; i++) {
            auto *stmt = reinterpret_cast<Stmt *>(block->get_child(i));
            if (stmt->type() == StatementType::Assert)
                stmts_to_remove.emplace_back(stmt->shared_from_this());
        }
        for (auto const &stmt : stmts_to_remove) {
            block->remove_stmt(stmt);
        }
    }
};

void remove_assertion(Generator *top) {
    AssertionRemoval visitor;
    visitor.visit_root(top);
    // then remove empty block
    remove_empty_block(top);
}

class ContinuousAssignVisitor : public IRVisitor {
public:
    void visit(Generator *top) override {
        std::vector<std::shared_ptr<Stmt>> assignments;
        uint32_t stmt_count = top->stmts_count();
        assignments.reserve(stmt_count);

        for (uint32_t i = 0; i < stmt_count; i++) {
            auto stmt = top->get_stmt(i);
            if (stmt->parent() == top && stmt->type() == StatementType::Assign) {
                assignments.emplace_back(stmt);
            }
        }

        if (!assignments.empty()) {
            for (auto const &stmt : assignments) {
                top->remove_stmt(stmt);
                auto comb = top->combinational();
                comb->add_stmt(stmt);
            }
        }
    }
};

void convert_continuous_stmt(Generator *top) {
    // this will change any top level assignment into
    // this has to be done after port decoupling
    ContinuousAssignVisitor visitor;
    visitor.visit_generator_root_p(top);
}

}  // namespace kratos
