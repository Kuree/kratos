#include "debug.hh"
#include "except.hh"
#include "fmt/format.h"
#include "generator.hh"
#include "sqlite_orm/sqlite_orm.h"
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
        if (var->size != 1) return;
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
    // we need to be careful about whether the top is included or not in the handle name
    bool initialized = false;
    bool has_top = false;
    for (auto const &[gen, map] : mapping) {
        if (!initialized) {
            auto handle_name = gen->handle_name();
            has_top = handle_name.find(top_name_) == std::string::npos;
            initialized = true;
        }
        auto handle_name = gen->handle_name();
        if (!has_top) handle_name = ::format("{0}.{1}", top_name_, handle_name);

        variable_mapping_.emplace(handle_name,
                                  std::make_pair(gen, std::map<std::string, std::string>()));

        for (auto const &[front_var_name, var] : map) {
            variable_mapping_[handle_name].second.emplace(front_var_name, var->to_string());
        }
    }
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
                for (const auto &[target_port, parent_var] : mapping) {
                    // we ignore the constant connection
                    if (parent_var->type() == VarType::ConstValue) continue;
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

class HierarchyVisitor: public IRVisitor {
public:
    void visit(Generator *generator) override  {
        auto handle_name = generator->handle_name();
        for (auto const &gen: generator->get_child_generators()) {
            auto name = gen->instance_name;
            hierarchy_.emplace_back(std::make_pair(handle_name, name));
        }
    }
    const std::vector<std::pair<std::string, std::string>> & hierarchy() const { return hierarchy_; }

private:
    std::vector<std::pair<std::string, std::string>> hierarchy_;
};

void DebugDatabase::set_generator_hierarchy(kratos::Generator *top) {
    HierarchyVisitor visitor;
    // no parallel to make it in order
    visitor.visit_generator_root(top);
    hierarchy_ = visitor.hierarchy();
}

// this is the database schema
// TABLE metadata
// NAME, VALUE
// this is essentially a key-value storage
// TABLE breakpoint
// BREAK_POINT_ID filename, line_number
// this is mapping a breakpoint id to a line in the front-end code
// TABLE variables
// generator_handle, var, front_var, breakpoint
// generator_handle + var is the var handle name, front_var comes from the variable name
// and breakpoint is the breakpoint id

// TABLE connection
// all the variables are the in the RTL form. You can cross search the variable
// to find out the python variable name, if any

// TABLE hierarchy. the parent uses full handle name, the child is the instance name
// you can make parent_handle.child to obtain the child handle name

void DebugDatabase::save_database(const std::string &filename) {
    using namespace sqlite_orm;
    auto storage = make_storage(
        filename,
        make_table("metadata", make_column("name", &MetaData::name),
                   make_column("value", &MetaData::value)),
        make_table("breakpoint", make_column("id", &BreakPoint::id),
                   make_column("filename", &BreakPoint::filename),
                   make_column("line_num", &BreakPoint::line_num)),
        make_table("variable", make_column("handle", &Variable::handle),
                   make_column("var", &Variable::var),
                   make_column("front_var", &Variable::front_var),
                   make_column("id", &Variable::id)),
        make_table("connection", make_column("handle_from", &Connection::handle_from),
                   make_column("var_from", &Connection::var_from),
                   make_column("handle_to", &Connection::handle_to),
                   make_column("var_to", &Connection::var_to)),
        make_table("hierarchy", make_column("parent_handle", &Hierarchy::parent_handle),
                   make_column("child", &Hierarchy::child)));

    storage.sync_schema();
    // insert tables
    // use transaction to speed up
    auto guard = storage.transaction_guard();
    // metadata
    MetaData top_name{"top_name", top_name_};
    storage.insert(top_name);
    // break points
    for (auto const &[stmt, id] : break_points_) {
        if (stmt_mapping_.find(stmt) != stmt_mapping_.end()) {
            auto const &[fn, ln] = stmt_mapping_.at(stmt);
            BreakPoint br{id, fn, ln};
            storage.insert(br);
        }
    }
    // variables
    for (auto const &[handle_name, gen_map] : variable_mapping_) {
        auto const &[gen, vars] = gen_map;
        for (auto const &[var, front_var] : vars) {
            // FIXME: this is a hack on id mapping
            if (generator_break_points_.find(gen) == generator_break_points_.end())
                // exit the loop
                break;
            auto ids = generator_break_points_.at(gen);
            for (auto const &id : ids) {
                Variable variable{handle_name, var, front_var, id};
                storage.insert(variable);
            }
        }
    }

    // connections
    for (auto const &[from, to]: connection_map_) {
        auto const [from_handle, from_var] = from;
        auto const [to_handle, to_var] = to;
        Connection conn{from_handle, from_var, to_handle, to_var};
        storage.insert(conn);
    }

    // hierarchy
    for (auto const &[handle, name]: hierarchy_) {
        Hierarchy h{handle, name};
        storage.insert(h);
    }

    guard.commit();
}

}  // namespace kratos
