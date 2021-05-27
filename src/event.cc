#include "event.hh"
#include "except.hh"

#include "generator.hh"

namespace kratos {

void remove_empty_block(Generator *top);

std::shared_ptr<EventTracingStmtWrapper> Event::fire(
    const std::map<std::string, const Var *> &fields) {
    auto stmt = std::make_shared<EventTracingStmtWrapper>(event_name_);
    for (auto const &[name, value] : fields) {
        stmt->add_event_field(name, value);
    }
    return stmt;
}

class EventVisitor : public IRVisitor {
public:
    void visit(AuxiliaryStmt *stmt) override {
        if (stmt->aux_type() != AuxiliaryType::EventGathering) return;
        auto event = stmt->as<EventTracingStmt>();
        auto expr = get_cond(stmt);
        stmts.emplace(event, expr);
    }

    // NOLINTNEXTLINE
    static std::shared_ptr<Var> get_cond(Stmt *stmt) {
        auto *ir_parent = stmt->parent();
        if (ir_parent->ir_node_kind() == IRNodeKind::GeneratorKind) {
            return nullptr;
        }
        auto *parent_stmt = reinterpret_cast<Stmt*>(ir_parent);
        std::shared_ptr<Var> expr;
        if (parent_stmt->type() == StatementType::If) {
            // need to figure out which block it belongs to
            auto *if_ = reinterpret_cast<IfStmt*>(parent_stmt);
            if (if_->then_body().get() == stmt) {
                expr = if_->predicate();
            } else {
                expr = if_->predicate()->r_not().shared_from_this();
            }
        } else if (parent_stmt->type() == StatementType::Switch) {
            auto *switch_ = reinterpret_cast<SwitchStmt*>(parent_stmt);
            // figure out which condition it is in. notice that we could be in the default
            // branch as well
            auto const &body = switch_->body();
            bool found = false;
            for (auto const &[cond, stmt_blk]: body) {
                if (stmt_blk.get() == stmt) {
                    // it's this condition
                    expr = cond;
                    found = true;
                    break;
                }
            }
            if (!found) {
                throw StmtException("Incorrect statement block stage", {stmt});
            }
            if (!expr) {
                // it's the default one. we nor them together
                std::shared_ptr<Var> or_;
                for (auto const &[cond, stmt_blk]: body) {
                    if (!or_) {
                        or_ = cond;
                    } else if (cond) {
                        or_ = or_->operator||(*cond).shared_from_this();
                    }
                }
                expr = or_->r_not().shared_from_this();
            }
        } else {
            return get_cond(parent_stmt);
        }
        auto rest_expr = get_cond(parent_stmt);
        if (rest_expr) {
            return expr->operator&&(*rest_expr).shared_from_this();
        } else {
            return expr;
        }
    }

    std::unordered_map<std::shared_ptr<EventTracingStmt>, std::shared_ptr<Var>> stmts;
};

std::unordered_map<std::shared_ptr<EventTracingStmt>, std::shared_ptr<Var>>
extract_event_fire_condition(Generator *top) {
    EventVisitor visitor;
    visitor.visit_root(top);
    return visitor.stmts;
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