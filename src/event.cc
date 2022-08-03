#include "event.hh"

#include <algorithm>

#include "except.hh"
#include "fmt/format.h"
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
        add_info(event);
    }

    void add_info(const std::shared_ptr<EventTracingStmt> &stmt) {
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
        i.fields = stmt->event_fields();
        i.stmt = stmt;

        info.emplace_back(i);
    }

    std::vector<EventInfo> info;
};

std::vector<EventInfo> extract_event_info(Generator *top) {
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

}  // namespace kratos