#include "event.hh"

#include <algorithm>

#include "except.hh"
#include "fmt/format.h"
#include "generator.hh"
#include "schema.hh"

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
        add_info(event, expr);
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
                std::vector<std::shared_ptr<Const>> conditions;
                conditions.reserve(body.size());
                for (auto const &[cond, stmt_blk] : body) {
                    if (cond) conditions.emplace_back(cond);
                }
                // sort conditions based on the value. it's guarantee to be unique
                // so no problems of overlap
                std::sort(
                    conditions.begin(), conditions.end(),
                    [](const std::shared_ptr<Const> &left, const std::shared_ptr<Const> &right) {
                        return left->value() < right->value();
                    });
                or_ = conditions[0];
                if (conditions.size() > 1) {
                    for (uint64_t i = 1; i < conditions.size(); i++) {
                        or_ = or_->operator||(*conditions[i]).shared_from_this();
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

    void add_info(const std::shared_ptr<EventTracingStmt> &stmt, const std::shared_ptr<Var> &cond) {
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
        i.stmt = stmt;

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
        auto stmt_count = block->size();
        std::vector<std::shared_ptr<Stmt>> stmts_to_remove;
        for (uint64_t i = 0; i < stmt_count; i++) {
            auto const &stmt = block->get_stmt(i);
            if (stmt->type() == StatementType::Auxiliary) {
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

std::string full_path(Var *var) {
    if (var->type() == VarType::ConstValue) {
        auto const &c = var->as<Const>();
        return fmt::format("{0}", c->value());
    } else {
        return var->handle_name();
    }
}

std::string fields_to_json(const std::map<std::string, std::shared_ptr<Var>> &vars) {
    // layman's json serializer
    std::string result = "{";
    std::vector<std::string> entries;
    entries.reserve(vars.size());
    for (auto const &[name, var] : vars) {
        entries.emplace_back(fmt::format(R"("{0}": "{1}")", name, full_path(var.get())));
    }
    auto content = fmt::format("{0}", fmt::join(entries.begin(), entries.end(), ", "));
    result.append(content);
    result.append("}");
    return result;
}

void save_events(hgdb::DebugDatabase &db, Generator *top) {
    // we first extract out every event statement
    auto infos = extract_event_fire_condition(top);
    // then for each info we create an entry for the db
    for (auto const &info : infos) {
        // need to serialize fields, matches etc
        auto condition = full_path(info.condition.get());
        auto fields = fields_to_json(info.fields);
        auto matches = fields_to_json(info.stmt->match_values());
        auto action = static_cast<uint32_t>(info.type);
        hgdb::store_event(db, info.name, info.transaction, condition, action, fields, matches,
                          info.stmt->stmt_id());
    }
}

}  // namespace kratos