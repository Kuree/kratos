#include "debug.hh"
#include "db.hh"
#include "except.hh"
#include "fmt/format.h"
#include "generator.hh"
#include "util.hh"

using fmt::format;

namespace kratos {

class DebugBreakInjectVisitor : public IRVisitor {
public:
    void visit(CombinationalStmtBlock *stmt) override { insert_statements(stmt); }

    void visit(SequentialStmtBlock *stmt) override { insert_statements(stmt); }

    void visit(ScopedStmtBlock *stmt) override { insert_statements(stmt); }

private:
    void insert_statements(StmtBlock *block) {
        auto parent = block->generator_parent();
        if (!parent->debug)
            // we only insert statements to the ones that has debug turned on
            return;
        std::vector<std::shared_ptr<Stmt>> new_blocks;
        new_blocks.reserve(block->size() * 2);
        // if it's a sequential block, we only inject one and link them together since non-blocking
        // assignments are evaluated simultaneously
        auto root_blk = get_root_block(block);
        if (root_blk->block_type() == StatementBlockType::Sequential) {
            // only need to insert one
            uint32_t stmt_id = count_++;
            for (auto const &stmt : *block) {
                stmt->set_stmt_id(stmt_id);
                new_blocks.emplace_back(stmt);
            }
            // append the actual bp_stmt
            auto bp_stmt = get_function_call_stmt(parent, stmt_id);
            bp_stmt->set_parent(block);
            new_blocks.emplace_back(bp_stmt);
        } else {
            for (auto const &stmt : *block) {
                uint32_t stmt_id = count_++;
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
        }

        // replace the content
        block->set_stmts(new_blocks);
    }

    std::shared_ptr<FunctionCallStmt> get_function_call_stmt(Generator *generator,
                                                             uint32_t stmt_id) {
        if (!generator->has_function(break_point_func_name)) {
            // create the function in the generator
            auto func = generator->dpi_function(break_point_func_name);
            func->input(var_name_, var_size_, false);
            func->set_port_ordering({{break_point_func_arg, 0}});
        }
        auto &id_const = constant(stmt_id, var_size_);
        auto &var = generator->call(break_point_func_name,
                                    {{var_name_, id_const.shared_from_this()}}, false);
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

    uint32_t count_ = 0;

    const std::string var_name_ = break_point_func_arg;
    const uint32_t var_size_ = 32;
};

void inject_debug_break_points(Generator *top) {
    DebugBreakInjectVisitor visitor;
    visitor.visit_root(top);
}

class ExtractDebugVisitor : public IRVisitor {
public:
    void visit(AssignStmt *stmt) override { extract_stmt_id(stmt); }
    void visit(ScopedStmtBlock *stmt) override { extract_stmt_id(stmt); }
    void visit(IfStmt *stmt) override { extract_stmt_id(stmt); }
    void visit(SwitchStmt *stmt) override { extract_stmt_id(stmt); }
    void visit(FunctionCallStmt *stmt) override { extract_stmt_id(stmt); }
    void visit(ReturnStmt *stmt) override { extract_stmt_id(stmt); }

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
        if (var->size() != 1) return;
        insert_str(var);
    }

private:
    void static insert_str(Var *var) { var->set_after_var_str_(" /*verilator public*/"); }
};

void insert_verilator_public(Generator *top) {
    InsertVerilatorPublic visitor;
    visitor.visit_root(top);
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

void DebugDatabase::set_generator_variable(
    const std::map<Generator *, std::map<std::string, std::string>> &values) {
    for (auto const &[gen, map] : values) {
        auto handle_name = gen->handle_name();
        for (auto const &[name, value] : map) {
            generator_values_[handle_name].emplace(name, value);
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
                    if (target_port->port_direction() == PortDirection::In) {
                        connections_.emplace(
                            std::make_pair(gen_handle, parent_var->to_string()),
                            std::make_pair(target_handle_name, target_port->to_string()));
                    } else {
                        connections_.emplace(
                            std::make_pair(target_handle_name, target_port->to_string()),
                            std::make_pair(gen_handle, parent_var->to_string()));
                    }
                }
            }
        }
    }

    const DebugDatabase::ConnectionMap &connections() const { return connections_; }

private:
    DebugDatabase::ConnectionMap connections_;
};

void DebugDatabase::set_generator_connection(kratos::Generator *top) {
    // we create a IR visitor to visit the generators
    ConnectionVisitor visitor;
    // this can be parallelized
    visitor.visit_generator_root_p(top);
    connection_map_ = visitor.connections();
}

class HierarchyVisitor : public IRVisitor {
public:
    void visit(Generator *generator) override {
        auto handle_name = generator->handle_name();
        for (auto const &gen : generator->get_child_generators()) {
            auto name = gen->instance_name;
            hierarchy_.emplace_back(std::make_pair(handle_name, name));
        }
    }
    const std::vector<std::pair<std::string, std::string>> &hierarchy() const { return hierarchy_; }

private:
    std::vector<std::pair<std::string, std::string>> hierarchy_;
};

void DebugDatabase::set_generator_hierarchy(kratos::Generator *top) {
    HierarchyVisitor visitor;
    // no parallel to make it in order
    visitor.visit_generator_root(top);
    hierarchy_ = visitor.hierarchy();
}

std::unordered_map<uint32_t, Generator *> build_id_map(
    const std::unordered_map<Generator *, std::set<uint32_t>> &map) {
    std::unordered_map<uint32_t, Generator *> result;
    for (auto const &[gen, ids] : map) {
        for (auto const &id : ids) {
            result.emplace(id, gen);
        }
    }
    return result;
}

void DebugDatabase::save_database(const std::string &filename) {
    auto storage = init_storage(filename);

    storage.sync_schema();
    // insert tables
    // use transaction to speed up
    auto guard = storage.transaction_guard();
    // metadata
    MetaData top_name{"top_name", top_name_};
    storage.insert(top_name);
    // break points
    auto id_to_gen = build_id_map(generator_break_points_);
    for (auto const &[stmt, id] : break_points_) {
        if (stmt_mapping_.find(stmt) != stmt_mapping_.end()) {
            auto const &[fn, ln] = stmt_mapping_.at(stmt);
            if (id_to_gen.find(id) == id_to_gen.end())
                throw InternalException(::format("Unable to find breakpoint {0}", id));
            auto gen = id_to_gen.at(id);
            auto handle_name = gen->handle_name();
            BreakPoint br{id, fn, ln, handle_name};
            storage.insert(br);
        }
    }
    // variables
    for (auto const &[handle_name, gen_map] : variable_mapping_) {
        auto const &[gen, vars] = gen_map;
        // FIXME: this is a hack on id mapping
        if (generator_break_points_.find(gen) == generator_break_points_.end())
            // exit the loop
            continue;
        for (auto const &[front_var, var] : vars) {
            auto gen_var = gen->get_var(var);
            if (!gen_var) throw InternalException(::format("Unable to get variable {0}", var));
            Variable variable{handle_name, var, front_var, gen_var->size(), gen_var->type(), true};
            storage.insert(variable);
        }
        auto all_vars = gen->get_all_var_names();
        for (auto const &var_name : all_vars) {
            auto var = gen->get_var(var_name);
            if (var && (var->type() == VarType::Base || var->type() == VarType::PortIO)) {
                Variable variable{handle_name, var_name, "", var->size(), var->type(), true};
                storage.insert(variable);
            }
        }
    }
    for (auto const &[handle_name, map] : generator_values_) {
        for (auto const &[name, value] : map) {
            Variable variable{handle_name, value, name, 0, 0, false};
            storage.insert(variable);
        }
    }

    // connections
    for (auto const &[from, to] : connection_map_) {
        auto const [from_handle, from_var] = from;
        auto const [to_handle, to_var] = to;
        Connection conn{from_handle, from_var, to_handle, to_var};
        storage.insert(conn);
    }

    // hierarchy
    for (auto const &[handle, name] : hierarchy_) {
        Hierarchy h{handle, name};
        storage.insert(h);
    }

    // local context variables
    for (auto const &[stmt, id] : break_points_) {
        // use breakpoint as an index since we can only get context as we hit potential breakpoints
        if (stmt_context_.find(stmt) == stmt_context_.end()) continue;
        auto values = stmt_context_.at(stmt);
        for (auto const &[key, entry] : values) {
            auto const &[is_var, value] = entry;
            ContextVariable v{key, value, is_var, id};
            storage.insert(v);
        }
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

}  // namespace kratos
