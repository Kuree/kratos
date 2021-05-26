#include "event.hh"
#include "generator.hh"


namespace kratos {

void remove_empty_block(Generator *top);

std::shared_ptr<EventGatheringStmtWrapper> Event::fire(
    const std::map<std::string, const Var *> &fields) {
    auto stmt = std::make_shared<EventGatheringStmtWrapper>(event_name_);
    for (auto const &[name, value] : fields) {
        stmt->add_event_field(name, value);
    }
    return stmt;
}

class EventRemoval : public IRVisitor {
public:
    void visit(Generator *gen) override {
        auto stmt_count = gen->stmts_count();
        std::vector<std::shared_ptr<Stmt>> stmts_to_remove;
        for (uint64_t i = 0; i < stmt_count; i++) {
            auto stmt = gen->get_stmt(i);
            if (stmt->type() == StatementType::Auxiliary) {
                auto aux = stmt->as<AuxiliaryStmt>();
                if (aux->aux_type() == AuxiliaryType::EventGathering)
                    stmts_to_remove.emplace_back(stmt);
            }
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
            if (stmt->type() == StatementType::Assert) {
                auto aux = stmt->as<AuxiliaryStmt>();
                if (aux->aux_type() == AuxiliaryType::EventGathering)
                    stmts_to_remove.emplace_back(stmt);
            }
        }
        for (auto const &stmt : stmts_to_remove) {
            block->remove_stmt(stmt);
        }
    }
};

void remove_event_stmts(Generator *top) {
    EventRemoval visitor;
    visitor.visit_root(top);
    // then remove empty block
    remove_empty_block(top);
}

}  // namespace kratos