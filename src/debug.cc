#include "debug.hh"
#include "generator.hh"

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
        if (!generator->has_function(break_point_func_name_)) {
            // create the function in the generator
            auto func = generator->dpi_function(break_point_func_name_);
            func->input(var_name_, var_size_, false);
            func->set_port_ordering({{"stmt_id", 0}});
            // it is a context function
            func->set_is_context(true);
        }
        auto &id_const = constant(stmt_id, var_size_);
        auto &var = generator->call(break_point_func_name_,
                                    {{var_name_, id_const.shared_from_this()}}, false);
        return std::make_shared<FunctionCallStmt>(var.as<FunctionCallVar>());
    }

    uint32_t count_ = 0;
    std::unordered_map<Stmt *, uint32_t> map_;
    const std::string break_point_func_name_ = "breakpoint_trace";
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

}