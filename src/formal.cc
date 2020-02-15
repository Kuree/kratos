#include "formal.hh"
#include "stmt.hh"

namespace kratos {

class AsyncVisitor: public IRVisitor {
public:
    void visit(Generator* gen) override {
        auto const stmt_count = gen->stmts_count();
        std::unordered_set<Port*> rst_ports;
        for (uint64_t i = 0; i < stmt_count; i++) {
            auto stmt = gen->get_stmt(i);
            if (stmt->type() == StatementType::Block) {
                auto stmt_blk = stmt->as<StmtBlock>();
                if (stmt_blk->block_type() == StatementBlockType::Sequential) {
                    auto seq = stmt_blk->as<SequentialStmtBlock>();
                    auto &conditions = seq->get_conditions();
                    std::set<decltype(conditions.begin())> reset_to_remove;
                    for (auto iter = conditions.begin(); iter != conditions.end(); iter++) {
                        auto var = iter->second;
                        if (var->type() != VarType::BaseCasted) {
                            if (var->type() == VarType::PortIO) {
                                auto port = var->as<Port>();
                                if (port->port_type() == PortType::AsyncReset) {
                                    // need to remove this one
                                    reset_to_remove.emplace(iter);
                                    rst_ports.emplace(port.get());
                                }
                            }
                        } else {
                            auto casted = var->as<VarCasted>();
                            if (casted->cast_type() == VarCastType::AsyncReset) {
                                // need to remove this one
                                reset_to_remove.emplace(iter);
                            }
                        }
                    }
                    for (auto const &iter: reset_to_remove) {
                        conditions.erase(iter);
                    }
                }
            }
        }

        for (auto const &var: rst_ports) {
            var->set_port_type(PortType::Reset);
        }
    }
};

void remove_async_reset(Generator* top) {
    AsyncVisitor visitor;
    visitor.visit_generator_root_p(top);
}
}