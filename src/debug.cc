#include "debug.hh"

#include <mutex>

#include "db.hh"
#include "except.hh"
#include "fmt/format.h"
#include "generator.hh"
#include "pass.hh"
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

private:
    void insert_statements(StmtBlock *block) {
        auto parent = block->generator_parent();
        if (!parent->debug)
            // we only insert statements to the ones that has debug turned on
            return;
        std::vector<std::shared_ptr<Stmt>> new_blocks;
        new_blocks.reserve(block->size() * 2);

        for (auto const &stmt : *block) {
            uint32_t stmt_id = context_->max_stmt_id()++;
            // make a function call
            auto bp_stmt = get_function_call_stmt(parent, stmt_id);
            // FIXME: See #89
            bp_stmt->set_parent(block);
            new_blocks.emplace_back(bp_stmt);
            // insert the normal one
            new_blocks.emplace_back(stmt);
            // set stmt id
            stmt->set_stmt_id(stmt_id);
        }

        // replace the content
        block->set_stmts(new_blocks);
    }

    std::shared_ptr<FunctionCallStmt> get_function_call_stmt(Generator *generator,
                                                             uint32_t stmt_id) {
        if (!generator->has_function(break_point_func_name)) {
            // create the function in the generator
            auto func = generator->dpi_function(break_point_func_name);
            func->input(break_point_instance_id_arg, var_size_, false);
            func->input(var_name_, var_size_, false);
            func->set_port_ordering({{break_point_instance_id_arg, 0}, {break_point_func_arg, 1}});
        }
        auto &id_const = constant(stmt_id, var_size_);
        auto i_id_const = generator->get_param(break_point_param_name);
        if (!i_id_const) {
            throw UserException(::format("{0} not found for {1}", break_point_param_name,
                                         generator->handle_name()));
        }
        auto &var = generator->call(
            break_point_func_name,
            {{var_name_, id_const.shared_from_this()}, {break_point_instance_id_arg, i_id_const}},
            false);
        return std::make_shared<FunctionCallStmt>(var.as<FunctionCallVar>());
    }

    static StmtBlock *get_root_block(Stmt *stmt) {
        if (stmt->type() == StatementType::Block) {
            auto block = reinterpret_cast<StmtBlock *>(stmt);
            if (block->block_type() != StatementBlockType::Scope) {
                return block;
            }
        }
        auto parent = stmt->parent();
        if (parent->ir_node_kind() != IRNodeKind::StmtKind) {
            throw InternalException("Non block statement's parent has to be a block statement");
        }
        auto parent_stmt = reinterpret_cast<Stmt *>(parent);
        return get_root_block(parent_stmt);
    }

    const std::string var_name_ = break_point_func_arg;
    const uint32_t var_size_ = 32;

    Context *context_;
};

void inject_debug_break_points(Generator *top) {
    DebugBreakInjectVisitor visitor(top->context());
    visitor.visit_root(top);
}

class InstanceIdVisitor : public IRVisitor {
public:
    explicit InstanceIdVisitor(Context *context) : context_(context), mutex_() {}

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

private:
    std::map<Stmt *, uint32_t> map_;
};

std::map<Stmt *, uint32_t> extract_debug_break_points(Generator *top) {
    ExtractDebugVisitor visitor;
    visitor.visit_root(top);
    return visitor.map();
}

class InsertVerilatorPublic : public IRVisitor {
public:
    void visit(Var *var) override {
        if (var->type() != VarType::Base) return;
        insert_str(var);
    }

    void visit(Port *var) override {
        // currently the runtime only support scalar variables
        if (var->size().size() != 1 || var->size().front() > 1) return;
        insert_str(var);
    }

private:
    void static insert_str(Var *var) { var->set_after_var_str_(" /*verilator public*/"); }
};

void insert_verilator_public(Generator *top) {
    InsertVerilatorPublic visitor;
    visitor.visit_root(top);
}

class VarSourceVisitor : public IRVisitor {
public:
    void visit(Var *var) override {
        if (map_.find(var) != map_.end()) return;
        auto const &sources = var->sources();
        for (auto const &stmt : sources) {
            auto right = stmt->right();
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
    auto names = get_tokens(instance_name, ".");
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
                auto gen = stmt->generator_parent();
                generator_break_points_[gen].emplace(id);
                break;
            }
        }
    }
    // set context
    context_ = top->context();
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

void DebugDatabase::set_generator_variable(
    const std::map<Generator *, std::map<std::string, std::string>> &values) {
    for (auto const &[gen, map] : values) {
        for (auto const &[name, value] : map) {
            generator_values_[gen].emplace(name, value);
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

class ConnectionVisitor : public IRVisitor {
public:
    void visit(Generator *generator) override {
        lock_.lock();
        generators_.emplace(generator);
        lock_.unlock();
        // loop through the module instance statement, where it holds the connection
        // information
        uint64_t child_count = generator->stmts_count();
        for (uint64_t i = 0; i < child_count; i++) {
            auto const stmt = generator->get_stmt(i);
            if (stmt->type() == StatementType::ModuleInstantiation) {
                auto mod = stmt->as<ModuleInstantiationStmt>();
                auto target = mod->target();
                auto target_handle_name = target->handle_name();
                auto mapping = mod->port_mapping();
                for (auto [target_port, parent_var] : mapping) {
                    // we ignore the constant connection
                    if (parent_var->type() != VarType::PortIO) {
                        if (target_port->port_direction() == PortDirection::In) {
                            auto source = parent_var->sources();
                            if (source.size() == 1) {
                                parent_var = (*source.begin())->right();
                            }
                        } else {
                            auto sink = parent_var->sinks();
                            if (sink.size() == 1) {
                                parent_var = (*sink.begin())->left();
                            }
                        }
                    }
                    if (parent_var->type() != VarType::PortIO) {
                        continue;
                    }
                    auto gen = parent_var->generator;
                    auto gen_handle = gen->handle_name();
                    // the direction is var -> var
                    lock_.lock();
                    if (target_port->port_direction() == PortDirection::In) {
                        connections_.emplace(
                            std::make_pair(gen_handle, parent_var->to_string()),
                            std::make_pair(target_handle_name, target_port->to_string()));
                    } else {
                        connections_.emplace(
                            std::make_pair(target_handle_name, target_port->to_string()),
                            std::make_pair(gen_handle, parent_var->to_string()));
                    }
                    lock_.unlock();
                }
            }
        }
    }

    const DebugDatabase::ConnectionMap &connections() const { return connections_; }
    const std::unordered_set<Generator *> &generators() const { return generators_; }

private:
    DebugDatabase::ConnectionMap connections_;
    std::unordered_set<Generator *> generators_;
    std::mutex lock_;
};

void DebugDatabase::set_generator_connection(kratos::Generator *top) {
    // we create a IR visitor to visit the generators
    ConnectionVisitor visitor;
    // this can be parallelized
    visitor.visit_generator_root_p(top);
    connection_map_ = visitor.connections();
    generators_ = visitor.generators();
}

class HierarchyVisitor : public IRVisitor {
public:
    void visit(Generator *generator) override {
        auto handle_name = generator->handle_name();
        for (auto const &gen : generator->get_child_generators()) {
            hierarchy_.emplace_back(std::make_pair(handle_name, gen.get()));
        }
    }
    const std::vector<std::pair<std::string, Generator *>> &hierarchy() const { return hierarchy_; }

private:
    std::vector<std::pair<std::string, Generator *>> hierarchy_;
};

void DebugDatabase::set_generator_hierarchy(kratos::Generator *top) {
    HierarchyVisitor visitor;
    // no parallel to make it in order
    visitor.visit_generator_root(top);
    hierarchy_ = visitor.hierarchy();
}

void DebugDatabase::save_database(const std::string &filename, bool override) {
    if (override) {
        if (fs::exists(filename)) {
            fs::remove(filename);
        }
    }
    auto storage = init_storage(filename);
    storage.sync_schema();
    // insert tables
    // use transaction to speed up
    auto guard = storage.transaction_guard();
    // metadata
    MetaData top_name{"top_name", top_name_};
    storage.insert(top_name);

    // insert generator ids
    std::unordered_map<Generator *, uint32_t> gen_id_map;
    std::unordered_map<std::string, uint32_t> handle_id_map;
    for (auto const &gen : generators_) {
        if (gen->generator_id < 0) {
            // assign a new ID
            gen->generator_id = gen->context()->max_instance_id()++;
        }
        int id = gen->generator_id;
        gen_id_map.emplace(gen, id);
        handle_id_map.emplace(gen->handle_name(), id);
        Instance inst{id, gen->handle_name()};
        storage.replace(inst);
    }

    // break points
    for (auto const &[stmt, id] : break_points_) {
        if (stmt_mapping_.find(stmt) != stmt_mapping_.end()) {
            auto const &[fn, ln] = stmt_mapping_.at(stmt);
            BreakPoint br{id, fn, ln};
            storage.replace(br);
        }
    }

    // variables
    int variable_count = 0;
    std::unordered_set<Var *> var_id_set;
    // function to create variable and flatten the hierarchy
    auto create_variable = [&](Var *var_, const int handle_id_, std::string name_,
                               const std::string &value_, bool is_context_,
                               uint32_t breakpoint_id_ = 0) {
        Variable v;
        v.is_var = var_ != nullptr;
        v.is_context = is_context_;
        v.handle = std::make_unique<int>(handle_id_);
        v.name = "";

        auto add_context = [&]() {
            if (is_context_) {
                // create context mapping as well
                ContextVariable c_v{std::make_unique<uint32_t>(breakpoint_id_),
                                    std::make_unique<int>(v.id), name_};
                storage.replace(c_v);
            }
        };

        if (var_) {
            // it is an variable
            if (var_->size().size() > 1 || var_->size().front() > 1) {
                // it's an array. need to flatten it
                // use recursion to do it
                std::function<void(const std::string &, const std::string &, uint32_t)>
                    add_data_point =
                        [&](const std::string &value, const std::string &name, uint32_t index) {
                            if (index >= var_->size().size()) return;
                            auto width = var_->size()[index];
                            for (uint32_t i = 0; i < width; i++) {
                                v.name = ::format("{0}.{1}", name, i);
                                v.value = ::format("{0}[{1}]", value, i);
                                v.id = variable_count++;
                                storage.replace(v);
                                add_context();

                                auto new_name = ::format("{0}.{1}", name, i);
                                auto new_value = ::format("{0}[1]", value, i);
                                add_data_point(new_name, new_value, index + 1);
                            }
                        };
                add_data_point(var_->name, name_, 0);
            } else if (var_->is_struct()) {
                // it's an packed array
                if (var_->type() == VarType::PortIO) {
                    auto p = reinterpret_cast<PortPackedStruct *>(var_);
                    auto const &def = p->packed_struct();
                    for (auto const &iter : def.attributes) {
                        auto const &attr_name = std::get<0>(iter);
                        // we need to store lots of them
                        if (!name_.empty()) v.name = ::format("{0}.{1}", name_, attr_name);
                        v.value = ::format("{0}.{1}", var_->name, attr_name);
                        v.id = variable_count++;
                        storage.replace(v);
                        add_context();
                    }
                } else if (var_->type() == VarType::Base) {
                    auto p = reinterpret_cast<VarPackedStruct *>(var_);
                    auto const &def = p->packed_struct();
                    for (auto const &iter : def.attributes) {
                        auto const &attr_name = std::get<0>(iter);
                        // we need to store lots of them
                        v.name = ::format("{0}.{1}", name_, attr_name);
                        v.value = ::format("{0}.{1}", var_->name, attr_name);
                        v.id = variable_count++;
                        storage.replace(v);
                        add_context();
                    }
                }
            } else {
                // the normal one
                v.name = name_;
                v.value = var_->name;
                v.id = variable_count++;
                storage.replace(v);
                add_context();
            }
            var_id_set.emplace(var_);
        } else {
            // directly store it
            if (name_.empty()) {
                throw UserException(::format("Non-variable cannot have empty name in database"));
            }
            v.name = name_;
            v.value = value_;
            v.id = variable_count++;
            storage.replace(v);
            add_context();
        }
    };
    for (auto const &[handle_name, gen_map] : variable_mapping_) {
        auto const &[gen, vars] = gen_map;
        if (gen_id_map.find(gen) == gen_id_map.end())
            throw InternalException(::format("Unable to find generator {0}", gen->handle_name()));
        auto id = gen_id_map.at(gen);
        for (auto const &[front_var, var] : vars) {
            auto gen_var = gen->get_var(var);
            if (!gen_var) throw InternalException(::format("Unable to get variable {0}", var));
            create_variable(gen_var.get(), id, front_var, "", false);
        }
        auto all_vars = gen->get_all_var_names();
        for (auto const &var_name : all_vars) {
            auto var = gen->get_var(var_name);
            // continue because we already have that variable stored
            if (var_id_set.find(var.get()) != var_id_set.end()) continue;
            if (var && (var->type() == VarType::Base || var->type() == VarType::PortIO)) {
                create_variable(var.get(), id, "", "", false);
            }
        }
    }
    for (auto const &[gen, map] : generator_values_) {
        auto const handle_name = gen->handle_name();
        if (handle_id_map.find(handle_name) == handle_id_map.end())
            throw InternalException(::format("Unable to find id for {0}", handle_name));
        auto id = handle_id_map.at(handle_name);
        for (auto const &[name, value] : map) {
            auto var = gen->get_var(name);
            create_variable(var.get(), id, name, value, false);
        }
    }

    // connections
    for (auto const &[from, to] : connection_map_) {
        auto const [from_handle, from_var] = from;
        auto const [to_handle, to_var] = to;
        if (handle_id_map.find(from_handle) == handle_id_map.end())
            throw InternalException(::format("Unable to find id for {0}", from_handle));
        if (handle_id_map.find(to_handle) == handle_id_map.end())
            throw InternalException(::format("Unable to find id for {0}", to_handle));
        auto from_id = handle_id_map.at(from_handle);
        auto to_id = handle_id_map.at(to_handle);
        Connection conn{std::make_unique<int>(from_id), from_var, std::make_unique<int>(to_id),
                        to_var};
        storage.replace(conn);
    }

    // hierarchy
    for (auto const &[handle, child] : hierarchy_) {
        if (handle_id_map.find(handle) == handle_id_map.end())
            throw InternalException(::format("Unable to find id for {0}", handle));
        if (handle_id_map.find(child->handle_name()) == handle_id_map.end())
            throw InternalException(::format("Unable to find id for {0}", child->handle_name()));
        auto id = handle_id_map.at(handle);
        auto child_id = handle_id_map.at(child->handle_name());
        Hierarchy h{std::make_unique<int>(id), child->instance_name,
                    std::make_unique<int>(child_id)};
        storage.replace(h);
    }

    // local context variables
    for (auto const &[stmt, id] : break_points_) {
        // use breakpoint as an index since we can only get context as we hit potential breakpoints
        auto const &gen = stmt->generator_parent();
        auto handle_name = gen->handle_name();
        if (stmt_context_.find(stmt) == stmt_context_.end()) continue;
        if (handle_id_map.find(handle_name) == handle_id_map.end())
            throw InternalException(::format("Unable to find {0} in handle id map", handle_name));

        auto instance_id = handle_id_map.at(handle_name);
        auto values = stmt_context_.at(stmt);

        for (auto const &[key, entry] : values) {
            auto const &[is_var, value] = entry;
            auto gen_var = is_var ? gen->get_var(value).get() : nullptr;
            create_variable(gen_var, instance_id, key, value, true, id);
        }
    }

    // instance id set
    for (auto const &[stmt, id] : break_points_) {
        auto gen_id = stmt->generator_parent()->generator_id;
        InstanceSetEntry entry{std::make_unique<int>(gen_id), std::make_unique<int>(id)};
        storage.replace(entry);
    }

    guard.commit();
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
            auto stmt = reinterpret_cast<AssertValueStmt *>(base);
            // create a function call
            auto gen = base->generator_parent();
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

    void process_block(StmtBlock *block) const {
        auto stmt_count = block->child_count();
        std::vector<std::shared_ptr<Stmt>> stmts_to_remove;
        for (uint64_t i = 0; i < stmt_count; i++) {
            auto stmt = reinterpret_cast<Stmt *>(block->get_child(i));
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
