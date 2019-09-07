#include "debug.hh"
#include "fmt/format.h"
#include "generator.hh"
#include "sqlite_orm/sqlite_orm.h"
#include "util.hh"

using fmt::format;

namespace kratos {

class DebugBreakInjectVisitor : public IRVisitor {
public:
    const std::unordered_map<Stmt *, uint32_t> &stmt_map() const { return map_; }

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
        for (auto const &stmt : *block) {
            uint32_t stmt_id = count_++;
            // make a function call
            auto bp_stmt = get_function_call_stmt(parent, stmt_id);
            // FIXME: See #89
            bp_stmt->set_parent(block);
            new_blocks.emplace_back(bp_stmt);
            map_.emplace(stmt.get(), stmt_id);
            // insert the normal one
            new_blocks.emplace_back(stmt);
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
            func->set_port_ordering({{"stmt_id", 0}});
            // it is a context function
            func->set_is_context(true);
        }
        auto &id_const = constant(stmt_id, var_size_);
        auto &var = generator->call(break_point_func_name,
                                    {{var_name_, id_const.shared_from_this()}}, false);
        return std::make_shared<FunctionCallStmt>(var.as<FunctionCallVar>());
    }

    uint32_t count_ = 0;
    std::unordered_map<Stmt *, uint32_t> map_;

    const std::string var_name_ = "stmt_id";
    const uint32_t var_size_ = 32;
};

std::unordered_map<Stmt *, uint32_t> inject_debug_break_points(Generator *top) {
    DebugBreakInjectVisitor visitor;
    visitor.visit_root(top);
    return visitor.stmt_map();
}

void insert_debugger_setup(Generator *top) {
    // create an initial block at the very end that calls a specialized DPI function
    const std::string func_name = "setup_debugger";
    auto initial = top->initial();
    auto func = top->dpi_function(func_name);
    // this is an context function
    func->set_is_context(true);
    auto &call_var = top->call(func_name, {}, false);
    auto stmt = std::make_shared<FunctionCallStmt>(call_var.as<FunctionCallVar>());
    initial->add_stmt(stmt);
}

void DebugDatabase::set_break_points(const std::map<Stmt *, uint32_t> &break_points) {
    set_break_points(break_points, ".py");
}

void DebugDatabase::set_break_points(const std::map<Stmt *, uint32_t> &break_points,
                                     const std::string &ext) {
    // set the break points
    break_points_ = break_points;

    // index all the front-end code
    // we are only interested in the files that has the extension
    for (auto const &[stmt, id] : break_points) {
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

struct MetaData {
    std::string name;
    std::string value;
};

struct BreakPoint {
    uint32_t id;
    std::string filename;
    uint32_t line_num;
};

struct Variable {
    std::string handle;
    std::string var;
    std::string front_var;
    uint32_t id;
};

void DebugDatabase::save_database(const std::string &filename) {
    using namespace sqlite_orm;
    auto storage =
        make_storage(filename,
                     make_table("metadata", make_column("name", &MetaData::name),
                                make_column("value", &MetaData::value)),
                     make_table("breakpoint", make_column("id", &BreakPoint::id, primary_key()),
                                make_column("filename", &BreakPoint::filename),
                                make_column("line_num", &BreakPoint::line_num)),
                     make_table("variable", make_column("handle", &Variable::handle),
                                make_column("var", &Variable::var),
                                make_column("front_var", &Variable::front_var),
                                make_column("id", &Variable::id)));
    // insert tables
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
}

}