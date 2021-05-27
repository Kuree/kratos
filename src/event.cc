#include "event.hh"

#include "except.hh"
#include "generator.hh"

namespace kratos {

void remove_empty_block(Generator *top);

std::shared_ptr<EventTracingStmt> Event::fire(
    const std::map<std::string, std::shared_ptr<Var>> &fields) {
    auto stmt = std::make_shared<EventTracingStmt>(event_name_);
    for (auto const &[name, value] : fields) {
        stmt->add_event_field(name, value);
    }
    return stmt;
}

class EventVisitor : public IRVisitor {
public:
    void visit(AuxiliaryStmt *stmt) override {
        if (stmt->aux_type() != AuxiliaryType::EventTracing) return;
        auto event = stmt->as<EventTracingStmt>();
        auto expr = get_cond(stmt);
        add_info(event.get(), expr);
    }

    // NOLINTNEXTLINE
    static std::shared_ptr<Var> get_cond(Stmt *stmt) {
        auto *ir_parent = stmt->parent();
        if (ir_parent->ir_node_kind() == IRNodeKind::GeneratorKind) {
            return nullptr;
        }
        auto *parent_stmt = reinterpret_cast<Stmt *>(ir_parent);
        std::shared_ptr<Var> expr;
        if (parent_stmt->type() == StatementType::If) {
            // need to figure out which block it belongs to
            auto *if_ = reinterpret_cast<IfStmt *>(parent_stmt);
            if (if_->then_body().get() == stmt) {
                expr = if_->predicate();
            } else {
                expr = if_->predicate()->r_not().shared_from_this();
            }
        } else if (parent_stmt->type() == StatementType::Switch) {
            auto *switch_ = reinterpret_cast<SwitchStmt *>(parent_stmt);
            // figure out which condition it is in. notice that we could be in the default
            // branch as well
            auto const &body = switch_->body();
            bool found = false;
            for (auto const &[cond, stmt_blk] : body) {
                if (stmt_blk.get() == stmt) {
                    // it's this condition
                    if (cond) expr = switch_->target()->eq(*cond).shared_from_this();
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
                for (auto const &[cond, stmt_blk] : body) {
                    if (!or_) {
                        or_ = cond;
                    } else if (cond) {
                        or_ = or_->operator||(*cond).shared_from_this();
                    }
                }
                expr = (switch_->target()->operator!=(*or_)).shared_from_this();
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

    void add_info(EventTracingStmt *stmt, const std::shared_ptr<Var> &cond) {
        bool combinational = true;
        auto *p = stmt->parent();

        while (p && p->ir_node_kind() == IRNodeKind::StmtKind) {
            auto *s = reinterpret_cast<Stmt *>(p);
            if (s->type() == StatementType::Block) {
                auto *b = reinterpret_cast<StmtBlock *>(s);
                if (b->block_type() == StatementBlockType::Sequential) {
                    combinational = false;
                    break;
                }
            }

            p = s->parent();
        }

        EventInfo i;
        i.name = stmt->event_name();
        i.transaction = stmt->transaction();
        i.combinational = combinational;
        i.type = stmt->action_type();
        i.condition = cond;
        i.fields = stmt->event_fields();

        info.emplace_back(i);
    }

    std::vector<EventInfo> info;
};

std::vector<EventInfo> extract_event_fire_condition(Generator *top) {
    EventVisitor visitor;
    visitor.visit_root(top);
    return visitor.info;
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
                if (aux->aux_type() == AuxiliaryType::EventTracing)
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
                if (aux->aux_type() == AuxiliaryType::EventTracing)
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