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
        std::vector<std::shared_ptr<Stmt>> new_blocks;
        new_blocks.reserve(block->size() * 2);
        for (auto const &stmt: *block) {
            uint32_t stmt_id = count_++;
            // make a function call
            auto bp_stmt = get_function_call_stmt(block->generator_parent());
            new_blocks.emplace_back(bp_stmt);
            map_.emplace(stmt.get(), stmt_id);
            // insert the normal one
            new_blocks.emplace_back(stmt);
        }
        // replace the content
        block->set_stmts(new_blocks);
    }

    std::shared_ptr<FunctionCallStmt> get_function_call_stmt(Generator* generator) {
        if (generator->has_function(break_point_func_name_)) {
            // create the function in the generator
            auto func = generator->dpi_function(break_point_func_name_);
            func->input("stmt_id", sizeof(uint32_t), false);
            func->set_port_ordering({{"stmt_id", 0}});
            // it is a context function
            func->set_is_context(true);
        }
        auto &var = generator->call(break_point_func_name_, {}, false);
        return std::make_shared<FunctionCallStmt>(var.as<FunctionCallVar>());
    }


    uint32_t count_ = 0;
    std::unordered_map<Stmt *, uint32_t> map_;
    const std::string break_point_func_name_ = "breakpoint_trace";
};

std::unordered_map<Stmt *, uint32_t> inject_debug_break_points(Generator *top) {
    DebugBreakInjectVisitor visitor;
    visitor.visit_root(top);
    return visitor.stmt_map();
}

}