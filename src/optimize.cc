#include "optimize.hh"

#include <algorithm>
#include <iostream>
#include <mutex>

#include "except.hh"
#include "fmt/format.h"
#include "stmt.hh"
#include "syntax.hh"
#include "util.hh"

using fmt::format;

namespace kratos {

class TransformIfCase : public IRVisitor {
public:
    void visit(CombinationalStmtBlock* stmts) override { transform_block(stmts); }
    void visit(SequentialStmtBlock* stmts) override { transform_block(stmts); }
    void visit(ScopedStmtBlock* stmts) override { transform_block(stmts); }

private:
    void static transform_block(StmtBlock* stmts) {
        auto const stmt_count = stmts->size();
        for (uint64_t i = 0; i < stmt_count; i++) {
            auto* stmt = stmts->get_stmt(i).get();
            Var* target = nullptr;
            std::vector<std::shared_ptr<IfStmt>> if_stmts;
            if (has_target_if(stmt, target, if_stmts) && target) {
                uint64_t cases = if_stmts.size();
                uint64_t expected_case = 1u << target->width();
                bool has_else = !(if_stmts.back()->else_body()->empty());
                if (expected_case > 1 && (cases >= expected_case || has_else)) {
                    auto switch_stmt = change_if_to_switch(stmt->as<IfStmt>(), if_stmts);
                    stmts->set_child(i, switch_stmt);
                }
            }
        }
    }
    bool static has_target_if(Stmt* stmt, Var*& var,
                              std::vector<std::shared_ptr<IfStmt>>& if_stmts) {
        // keep track of which statement are used later to transform into switch statement
        if (stmt->type() != StatementType::If && if_stmts.size() <= 1)
            return false;
        else if (stmt->type() != StatementType::If) {
            // we have reach the end of the if-else chain
            return true;
        }
        auto if_ = stmt->as<IfStmt>();
        auto predicate = if_->predicate();
        // predicate has to be a expression with equal comparison
        if (predicate->type() != VarType::Expression) return false;
        auto expr = predicate->as<Expr>();
        if (expr->op != ExprOp::Eq) return false;
        // has to be the same variable
        if (var == nullptr) {
            var = expr->left;
        } else {
            if (var != expr->left) return false;
        }
        if ((expr->right->type() != VarType::ConstValue) &&
            (expr->right->type() != VarType::Parameter))
            return false;
        if (if_->else_body()->size() > 1) return false;

        if_stmts.emplace_back(if_);
        if (if_->else_body()->empty()) {
            return true;
        } else {
            return has_target_if((*if_->else_body())[0].get(), var, if_stmts);
        }
    }

    std::shared_ptr<SwitchStmt> static change_if_to_switch(
        std::shared_ptr<IfStmt> stmt, const std::vector<std::shared_ptr<IfStmt>>& if_stmts) {
        auto expr = stmt->predicate()->as<Expr>();
        // we assume that this is a valid case (see has_target_if)
        auto* target = expr->left;
        std::shared_ptr<SwitchStmt> switch_ =
            std::make_shared<SwitchStmt>(target->shared_from_this());
        if (target->generator()->debug) {
            switch_->fn_name_ln = std::vector<std::pair<std::string, uint32_t>>(
                stmt->fn_name_ln.begin(), stmt->fn_name_ln.end());
            switch_->fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
        }

        while (std::find(if_stmts.begin(), if_stmts.end(), stmt) != if_stmts.end()) {
            auto condition = expr->right->as<Const>();
            switch_->add_switch_case(condition, stmt->then_body());
            if (!stmt->else_body()->empty() &&
                std::find(if_stmts.begin(), if_stmts.end(), (*stmt->else_body())[0]) ==
                    if_stmts.end()) {
                // we have reached the end
                // add default statement
                switch_->add_switch_case(nullptr, stmt->else_body());
                break;
            } else if (!stmt->else_body()->empty()) {
                // switch to the else case
                stmt = (*stmt->else_body())[0]->as<IfStmt>();
                expr = stmt->predicate()->as<Expr>();
            } else {
                break;
            }
        }

        return switch_;
    }
};

void transform_if_to_case(Generator* top) {
    TransformIfCase visitor;
    visitor.visit_root(top);
}

class MergeIfVisitor : public IRVisitor {
public:
    void visit(CombinationalStmtBlock* stmts) override { transform_block(stmts); }
    void visit(SequentialStmtBlock* stmts) override { transform_block(stmts); }
    void visit(ScopedStmtBlock* stmts) override { transform_block(stmts); }

private:
    using IfStmtType = std::pair<std::shared_ptr<IfStmt>, std::shared_ptr<Const>>;
    // The if statements has to satisfy the following requirements in order to merge
    // in the same block
    // if target is the same
    // all equality comparison and against an constant
    void static transform_block(StmtBlock* block) {
        // only run marked ones
        if (!block->has_attribute("merge_if_block")) return;
        std::map<Var*, std::vector<IfStmtType>> result;
        get_targeted_if(block, result);
        std::unordered_set<IfStmt*> merged_if;
        for (auto const& iter : result) {
            auto stmts = iter.second;
            if (stmts.size() > 1) {
                // we have stmts to merge
                auto top_if = stmts[0].first;
                // first pass to merge the if statements with the same constant value
                // build index on the const values
                std::unordered_map<int64_t, IfStmt*> mapping;
                for (const auto& [stmt, const_] : stmts) {
                    auto const_value = const_->value();
                    if (mapping.find(const_value) == mapping.end()) {
                        mapping.emplace(const_value, stmt.get());
                    } else {
                        // merge the current one into the one we already have
                        auto* if_ = mapping.at(const_value);
                        auto const& then = stmt->then_body();
                        for (auto const& st : *then) {
                            if_->add_then_stmt(st);
                        }
                        auto const& else_ = stmt->else_body();
                        for (auto const& st : *else_) {
                            if_->add_else_stmt(st);
                        }
                        merged_if.emplace(stmt.get());
                    }
                }

                // second pass to nest the if statement
                for (uint64_t i = 1; i < stmts.size(); i++) {
                    auto const& stmt = stmts[i].first;
                    if (merged_if.find(stmt.get()) != merged_if.end()) {
                        continue;
                    }
                    // put the one in the top if
                    top_if->add_else_stmt(stmt);
                    merged_if.emplace(stmt.get());
                }
            }
        }
        // remove merged if
        for (auto const& stmt : merged_if) {
            block->remove_stmt(stmt->shared_from_this());
        }
    }

    void static get_targeted_if(StmtBlock* block, std::map<Var*, std::vector<IfStmtType>>& result) {
        for (auto const& stmt : *block) {
            if (stmt->type() == StatementType::If) {
                auto if_ = stmt->as<IfStmt>();
                auto predicate = if_->predicate();
                if (predicate->type() == VarType::Expression) {
                    auto expr = predicate->as<Expr>();
                    if (expr->op == ExprOp::Eq && expr->right &&
                        expr->right->type() == VarType::ConstValue) {
                        // this is what we want
                        auto* target_var = expr->left;
                        result[target_var].emplace_back(
                            std::make_pair(if_, expr->right->as<Const>()));
                    }
                }
            }
        }
    }
};

void merge_if_block(Generator* top) {
    MergeIfVisitor visitor;
    visitor.visit_root(top);
}

class VarFanOutVisitor : public IRVisitor {
public:
    void visit(Generator* generator) override {
        auto var_names = generator->get_all_var_names();
        for (auto const& var_name : var_names) {
            auto var = generator->get_var(var_name);
            std::vector<std::pair<std::shared_ptr<Var>, std::shared_ptr<AssignStmt>>> chain;
            compute_assign_chain(var, chain);
            if (chain.size() <= 2) continue;  // nothing to be done

            std::vector<std::pair<std::string, uint32_t>> debug_info;

            for (uint64_t i = 0; i < chain.size() - 1; i++) {
                auto& [pre, stmt] = chain[i];
                auto next = chain[i + 1].first;

                // insert debug info
                if (generator->debug) {
                    debug_info.insert(debug_info.end(), stmt->fn_name_ln.begin(),
                                      stmt->fn_name_ln.end());
                }

                next->unassign(stmt);
            }

            auto dst = chain.back().first;
            Var::move_src_to(var.get(), dst.get(), generator, false);
            // if both of them are ports, we need to add a statement
            if (var->type() == VarType::PortIO && dst->type() == VarType::PortIO) {
                // need to add a top assign statement
                auto stmt = dst->assign(var, AssignmentType::Blocking);
                if (generator->debug) {
                    // copy every vars definition over
                    stmt->fn_name_ln = debug_info;
                    stmt->fn_name_ln.emplace_back(__FILE__, __LINE__);
                }
                generator->add_stmt(stmt);
            }
        }
    }

    void static compute_assign_chain(
        const std::shared_ptr<Var>& var,
        std::vector<std::pair<std::shared_ptr<Var>, std::shared_ptr<AssignStmt>>>& queue) {
        if (var->sinks().size() == 1) {
            auto const& stmt = *(var->sinks().begin());
            if (!stmt->parent()) return;
            if (stmt->parent()->ir_node_kind() == IRNodeKind::GeneratorKind) {
                auto* sink_var = stmt->left();
                if (sink_var->parent() != var->parent() || sink_var->is_interface()) {
                    // not the same parent
                    return;
                }
                // FIXME: need to re-work on fanout one wire removal
                //  For now disable the expression based search
                if (stmt->right() != var.get()) {
                    // expr based
                    return;
                }
                queue.emplace_back(std::make_pair(var, stmt));
                compute_assign_chain(sink_var->shared_from_this(), queue);
            }
        } else {
            queue.emplace_back(std::make_pair(var, nullptr));
        }
    }
};

void remove_fanout_one_wires(Generator* top) {
    VarFanOutVisitor visitor;
    visitor.visit_generator_root_p(top);
}

class RemovePassThroughVisitor : public IRVisitor {
public:
    void visit(Generator* generator) override {
        const auto& children = generator->get_child_generators();
        std::vector<std::shared_ptr<Generator>> child_to_remove;
        for (auto const& child : children) {
            if (is_pass_through(child.get())) {
                // need to remove it
                child_to_remove.emplace_back(child);
                // add it to the set
                if (!child->is_cloned()) pass_through_.emplace(child.get());
            }
        }

        for (auto const& child : child_to_remove) {
            // we move the src and sinks around
            const auto& port_names = child->get_port_names();
            for (auto const& port_name : port_names) {
                auto port = child->get_port(port_name);
                if (port->port_direction() == PortDirection::In) {
                    // move the src to whatever it's connected to
                    // basically compress the module into a variable
                    // we will let the later downstream passes to remove the extra wiring
                    auto* next_port = (*(port->sinks().begin()))->left();
                    auto var_name =
                        generator->get_unique_variable_name(child->instance_name, port->name);
                    auto& new_var = generator->var(var_name, port->var_width(), port->size(),
                                                   port->is_signed());
                    if (generator->debug) {
                        // need to copy the changes over
                        new_var.fn_name_ln = std::vector<std::pair<std::string, uint32_t>>(
                            child->fn_name_ln.begin(), child->fn_name_ln.end());
                        new_var.fn_name_ln.emplace_back(__FILE__, __LINE__);
                    }
                    Var::move_src_to(port.get(), &new_var, generator, false);
                    // move the sinks over
                    Var::move_sink_to(next_port, &new_var, generator, false);
                }
            }
            // remove it from the generator children
            generator->remove_child_generator(child->shared_from_this());
        }
    }

private:
    bool is_pass_through(Generator* generator) {
        if (generator->is_cloned()) {
            auto* ref_gen = generator->def_instance();
            if (!ref_gen) {
                throw GeneratorException(::format("{0} is cloned but doesn't have def instance",
                                                  generator->instance_name),
                                         {generator});
            }
            return pass_through_.find(ref_gen) != pass_through_.end();
        }
        const auto vars = generator->get_vars();
        // has to be empty
        if (!vars.empty()) return false;
        // has to have exact number of assignments as ports
        // ports has to be an even number, i.e. one in to one out
        // maybe we can relax this restriction later
        auto const port_names = generator->get_port_names();
        if (port_names.size() % 2) return false;
        if (generator->stmts_count() != port_names.size() / 2) return false;

        // NOLINTNEXTLINE
        for (const auto& port_name : port_names) {
            auto const port = generator->get_port(port_name);
            if (port->port_direction() == PortDirection::In) {
                auto sinks = port->sinks();
                if (sinks.size() != 1) return false;
            } else {
                auto const& sources = port->sources();
                if (sources.size() != 1) return false;
                // maybe some add stuff
                auto stmt = *(sources.begin());
                auto* src = stmt->right();
                if (src->type() != VarType::PortIO) return false;
            }
        }
        return true;
    }

    std::unordered_set<Generator*> pass_through_;
};

void remove_pass_through_modules(Generator* top) {
    RemovePassThroughVisitor visitor;
    visitor.visit_generator_root(top);
}

class MergeWireAssignmentsVisitor : public IRVisitor {
public:
    void visit(ScopedStmtBlock* block) override { process_stmt_block(block); }

    void visit(SequentialStmtBlock* block) override { process_stmt_block(block); }

    void visit(CombinationalStmtBlock* block) override { process_stmt_block(block); }

    void visit(Generator* generator) override {
        std::set<std::shared_ptr<Stmt>> stmts_to_remove;

        // first filter out sliced assignments
        std::set<std::shared_ptr<AssignStmt>> sliced_stmts;
        extract_sliced_stmts(generator, sliced_stmts);
        get_stmts_to_remove(generator, stmts_to_remove, sliced_stmts);

        // remove them
        for (auto const& stmt : stmts_to_remove) {
            generator->remove_stmt(stmt);
        }
    }

private:
    void process_stmt_block(StmtBlock* block) {
        std::set<std::shared_ptr<Stmt>> stmts_to_remove;

        // first filter out sliced assignments
        std::set<std::shared_ptr<AssignStmt>> sliced_stmts;
        extract_sliced_stmts(block, sliced_stmts);
        get_stmts_to_remove(block, stmts_to_remove, sliced_stmts);
        for (auto const& stmt : stmts_to_remove) block->remove_stmt(stmt);
    }

    static void extract_sliced_stmts(Generator* generator,
                                     std::set<std::shared_ptr<AssignStmt>>& sliced_stmts) {
        uint64_t stmt_count = generator->stmts_count();
        for (uint64_t i = 0; i < stmt_count; i++) {
            auto stmt = generator->get_stmt(i);
            if (stmt->type() == StatementType::Assign) {
                auto assign_stmt = stmt->as<AssignStmt>();
                if (assign_stmt->left()->type() == VarType::Slice &&
                    assign_stmt->right()->type() == VarType::Slice) {
                    sliced_stmts.emplace(assign_stmt);
                }
            }
        }
    }

    static void extract_sliced_stmts(StmtBlock* block,
                                     std::set<std::shared_ptr<AssignStmt>>& sliced_stmts) {
        for (auto const& stmt : *block) {
            if (stmt->type() == StatementType ::Assign) {
                auto assign_stmt = stmt->as<AssignStmt>();
                if (assign_stmt->left()->type() == VarType::Slice &&
                    assign_stmt->right()->type() == VarType::Slice) {
                    sliced_stmts.emplace(assign_stmt);
                }
            }
        }
    }

    template <typename T>
    void get_stmts_to_remove(T* generator, std::set<std::shared_ptr<Stmt>>& stmts_to_remove,
                             const std::set<std::shared_ptr<AssignStmt>>& sliced_stmts) const {
        // group the assignments together
        using AssignPair = std::pair<Var*, Var*>;
        std::map<AssignPair, std::vector<std::shared_ptr<AssignStmt>>> slice_vars;
        for (auto const& assign_stmt : sliced_stmts) {
            auto left_slice = assign_stmt->left()->as<VarSlice>();
            auto right_slice = assign_stmt->right()->as<VarSlice>();
            Var* left_parent = left_slice->parent_var;
            Var* right_parent = right_slice->parent_var;
            // only deal with 1D for now
            if (left_parent->type() == VarType::Slice) continue;
            if (right_parent->type() == VarType::Slice) continue;
            if (left_parent->width() != right_parent->width()) continue;
            if (left_parent->size().size() != right_parent->size().size() ||
                left_parent->size().front() != right_parent->size().front())
                continue;

            slice_vars[{left_parent, right_parent}].emplace_back(assign_stmt);
        }

        // merge the assignments
        for (auto const& [vars, stmts] : slice_vars) {
            const auto& [left, right] = vars;

            // NOTE:
            // we assume that at this stage we've passed the connectivity check
            if (stmts.size() != left->width()) continue;

            // remove left's sources and right's sink
            // also add it to the statements to remove
            for (auto const& stmt : stmts) {
                left->remove_source(stmt);
                right->remove_sink(stmt);
                stmts_to_remove.emplace(stmt);
            }
            // make new assignment
            create_new_assignment(generator, stmts, left, right);
        }
    }
    void static create_new_assignment(Generator* generator,
                                      const std::vector<std::shared_ptr<AssignStmt>>& stmts,
                                      Var* const left, Var* const right) {
        if (stmts.empty()) return;
        auto new_stmt = left->assign(right->shared_from_this(), AssignmentType::Blocking);
        generator->add_stmt(new_stmt);
        if (generator->debug) {
            // merge all the statements
            for (auto const& stmt : stmts) {
                new_stmt->fn_name_ln.insert(new_stmt->fn_name_ln.end(), stmt->fn_name_ln.begin(),
                                            stmt->fn_name_ln.end());
            }
            new_stmt->fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
        }
    }

    static void create_new_assignment(StmtBlock* block,
                                      const std::vector<std::shared_ptr<AssignStmt>>& stmts,
                                      Var* const left, Var* const right) {
        if (stmts.empty()) return;
        // use the first assignment type. assume all the assignment has passed the
        // mixed assignment check
        auto new_stmt = left->assign(right->shared_from_this(), stmts[0]->assign_type());
        block->add_stmt(new_stmt);
        auto* generator = get_parent(block);
        if (generator->debug) {
            // merge all the statements
            for (auto const& stmt : stmts) {
                new_stmt->fn_name_ln.insert(new_stmt->fn_name_ln.end(), stmt->fn_name_ln.begin(),
                                            stmt->fn_name_ln.end());
            }
            new_stmt->fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
        }
    }

    static Generator* get_parent(StmtBlock* block) {
        Generator* result = nullptr;
        IRNode* node = block;
        for (uint32_t i = 0; i < 10000u; i++) {
            auto* p = node->parent();
            if (p->ir_node_kind() == IRNodeKind::GeneratorKind) {
                result = dynamic_cast<Generator*>(p);
                break;
            }
            node = p;
        }
        if (!result) {
            throw StmtException("Cannot find parent for the statement block", {block});
        }
        return result;
    }
};

void merge_wire_assignments(Generator* top) {
    // for now we only merge generator-level assignments
    MergeWireAssignmentsVisitor visitor;
    visitor.visit_root(top);
}

class PipelineInsertionVisitor : public IRVisitor {
public:
    void visit(Generator* generator) override {
        // only if the generator has attribute of "pipeline" and the value string is the
        // number of pipeline stages will do
        bool has_attribute = false;
        std::string clock_name;
        auto attributes = generator->get_attributes();
        uint32_t num_stages = 0;
        for (auto const& attr : attributes) {
            if (attr->type_str == "pipeline") {
                try {
                    int i = std::stoi(attr->value_str);
                    if (i > 0) {
                        num_stages = static_cast<uint32_t>(i);
                        has_attribute = true;
                    }
                } catch (std::invalid_argument const&) {
                    throw std::runtime_error(
                        ::format("Unable to get value string from generator {0}", generator->name));
                }
            } else if (attr->type_str == "pipeline_clk") {
                clock_name = attr->value_str;
            }
        }
        if (has_attribute) {
            auto port_names = generator->get_port_names();
            // get the clock name, if it's empty
            if (clock_name.empty()) {
                // pick the first one
                auto clock_names = generator->get_ports(PortType::Clock);
                if (!clock_names.empty()) clock_name = clock_names[0];
            }
            if (clock_name.empty()) {
                throw GeneratorException(
                    ::format("Unable to find clock signal for generator {0}", generator->name),
                    {generator});
            }
            auto clock_port = generator->get_port(clock_name);
            // we need to create all the registers based on the posedge of the clock
            std::vector<std::shared_ptr<SequentialStmtBlock>> blocks;
            blocks.resize(num_stages);
            for (uint32_t i = 0; i < num_stages; i++) {
                blocks[i] = std::make_shared<SequentialStmtBlock>();
                generator->add_stmt(blocks[i]);
                blocks[i]->add_condition({BlockEdgeType::Posedge, clock_port});
                if (generator->debug)
                    blocks[i]->fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
            }
            // get all the outputs
            for (auto const& port_name : port_names) {
                auto port = generator->get_port(port_name);
                if (port->port_direction() == PortDirection::In) {
                    continue;
                }
                std::vector<std::shared_ptr<Var>> vars;
                vars.resize(num_stages);
                for (uint32_t i = 0; i < num_stages; i++) {
                    auto new_name =
                        generator->get_unique_variable_name(port_name, ::format("stage_{0}", i));
                    auto& var = generator->var(new_name, port->var_width(), port->size(),
                                               port->is_signed());
                    if (generator->debug)
                        var.fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
                    vars[i] = var.shared_from_this();
                }
                // move the source to the first stage
                Var::move_src_to(port.get(), vars[0].get(), generator, false);
                // connect the stages together
                for (uint32_t i = 0; i < num_stages - 1; i++) {
                    auto pre_stage = vars[i];
                    auto next_stage = vars[i + 1];
                    blocks[i]->add_stmt(next_stage->assign(pre_stage, AssignmentType::NonBlocking));
                }
                // last stage
                blocks[num_stages - 1]->add_stmt(
                    port->assign(vars[num_stages - 1], AssignmentType::NonBlocking));
            }
        }
    }
};

void insert_pipeline_stages(Generator* top) {
    PipelineInsertionVisitor visitor;
    visitor.visit_generator_root_p(top);
}

bool static has_port_type(Var* var, PortType type) {
    if (var->type() == VarType::Expression) {
        auto* expr = reinterpret_cast<Expr*>(var);
        auto l = has_port_type(expr->left, type);
        if (expr->right) {
            auto r = has_port_type(expr->right, type);
            return l && r;
        }
        return l;
    }
    if (var->type() == VarType::PortIO) {
        auto* p = reinterpret_cast<Port*>(var);
        return p->port_type() == type;
    } else if (var->type() == VarType::BaseCasted) {
        auto* casted = reinterpret_cast<VarCasted*>(var);
        if (type == PortType::AsyncReset)
            return casted->cast_type() == VarCastType::AsyncReset;
        else if (type == PortType::ClockEnable)
            return casted->cast_type() == VarCastType::ClockEnable;
        else if (type == PortType::Clock)
            return casted->cast_type() == VarCastType::Clock;
    }
    return false;
}

static std::shared_ptr<IfStmt> create_if_stmt_wrapper(StmtBlock* block, Port& port,
                                                      bool clone = false) {
    auto if_ = std::make_shared<IfStmt>(port);
    std::vector<std::shared_ptr<Stmt>> stmts;
    for (auto const& stmt : *block) {
        stmts.emplace_back(clone ? stmt->clone() : stmt);
    }
    if (!clone) block->clear();
    for (auto& stmt : stmts) {
        if (!clone) stmt->remove_from_parent();
        if_->add_then_stmt(stmt);
    }
    return if_;
}

class InsertClockIRVisitor : public IRVisitor {
public:
    static constexpr auto dont_touch = "dont_touch";
    explicit InsertClockIRVisitor(Generator* top) : top_(top) {
        // find out the top clock enable signal
        auto ports = top->get_ports(PortType::ClockEnable);
        // LCOV_EXCL_START
        if (ports.empty()) {
            clk_en_ = nullptr;
        } else if (ports.size() > 1) {
            throw UserException("Current the pass only support one clock enable signal in top");
        } else {
            // LCOV_EXCL_STOP
            clk_en_name_ = ports[0];
            clk_en_ = top->get_port(clk_en_name_).get();
        }
    }

    void visit(Generator* gen) override {
        if (!clk_en_) return;
        if (has_don_touch(gen)) return;
        if (gen->external() || gen->is_stub()) return;
        auto* parent = gen->parent_generator();
        if (!parent || gen == top_) return;

        Port* clk_en;
        if (!gen->has_port(clk_en_name_)) {
            clk_en = &gen->port(*clk_en_);
            if (clk_en->port_type() != PortType::ClockEnable)
                clk_en->set_port_type(PortType::ClockEnable);
        } else {
            clk_en = gen->get_port(clk_en_name_).get();
            // notice that if it's being wired to a constant, we need to disconnect it
            auto const& sources = clk_en->sources();
            if (!sources.empty()) {
                if ((*(sources.begin()))->right()->type() == VarType::ConstValue) {
                    auto stmt = *(sources.begin());
                    clk_en->clear_sources(true);
                } else {
                    // no need to wire
                    return;
                }
            }
        }
        // wire to the top
        auto parent_port = parent->get_port(clk_en_name_);
        parent->wire(*clk_en, *parent_port);
    }

    void visit(SequentialStmtBlock* block) override {
        if (!clk_en_) return;
        if (has_don_touch(block)) return;
        auto* gen = block->generator_parent();
        if (has_don_touch(gen)) return;
        auto num_stmts = block->size();
        auto* generator = block->generator_parent();
        auto clk_en = generator->get_port(clk_en_name_);
        if (num_stmts > 0) {
            // we need to be careful about async reset logic
            auto first_stmt = block->get_stmt(0);
            if (num_stmts == 1 && first_stmt->type() == StatementType::If) {
                // async reset?
                auto if_ = first_stmt->as<IfStmt>();
                auto cond = if_->predicate();
                if (has_port_type(cond.get(), PortType::AsyncReset) ||
                    has_port_type(cond.get(), PortType::Reset)) {
                    if (!has_clk_en_stmt(if_->else_body().get())) {
                        auto new_if = create_if_stmt_wrapper(if_->else_body().get(), *clk_en, true);
                        if_->else_body()->clear();
                        if_->add_else_stmt(new_if);
                    }
                    return;
                }
            }
            // put everything into one block
            // if not clk enabled already
            if (!has_clk_en_stmt(block)) {
                auto if_ = create_if_stmt_wrapper(block, *clk_en, true);
                block->clear();
                block->add_stmt(if_);
            }
        }
    }

private:
    std::string clk_en_name_;
    Port* clk_en_;
    Generator* top_;

    bool has_clk_en_stmt(StmtBlock* block) const {
        if (!block->empty()) {
            auto stmt = block->get_stmt(0);
            if (stmt->type() == StatementType::If) {
                auto if_ = stmt->as<IfStmt>();
                auto cond = if_->predicate();
                if (cond->type() == VarType::PortIO) {
                    auto p = cond->as<Port>();
                    if (p->port_type() == PortType::ClockEnable) {
                        return true;
                    }
                } else if (cond->type() == VarType::BaseCasted) {
                    auto casted = cond->as<VarCasted>();
                    return casted->cast_type() == VarCastType::ClockEnable;
                } else if (cond->name == clk_en_name_) {
                    return true;
                }
            }
        }
        return false;
    }

    static bool has_don_touch(const IRNode* node) {
        auto const& attrs = node->get_attributes();
        return std::any_of(attrs.begin(), attrs.end(),
                           [](auto const& a) { return a->value_str == dont_touch; });
    }
};

void auto_insert_clock_enable(Generator* top) {
    InsertClockIRVisitor visitor(top);
    visitor.visit_root(top);
}

class InsertSyncReset : public IRVisitor {
public:
    explicit InsertSyncReset(Generator* gen) {
        auto const& attributes = gen->get_attributes();
        for (auto const& attr : attributes) {
            auto const& value = attr->value_str;
            if (value.size() > sync_reset_name.size()) {
                if (value.substr(0, sync_reset_name.size()) == sync_reset_name) {
                    // get reset_name
                    auto tokens = string::get_tokens(value, ";");
                    auto first_token = tokens[0];
                    {
                        auto token_values = string::get_tokens(first_token, "=");
                        if (token_values.size() == 2) {
                            auto var_name = token_values[1];
                            if (is_valid_variable_name(var_name)) {
                                run_pass_ = true;
                                reset_name_ = var_name;
                            }
                        }
                    }
                    if (tokens.size() == 2) {
                        auto param_value = tokens[1];
                        auto token_values = string::get_tokens(param_value, "=");
                        if (token_values.size() == 2 && token_values[0] == "over_clk_en") {
                            if (token_values[1] == "true" || token_values[1] == "1") {
                                over_clk_en_ = true;
                            }
                        }
                    }
                }
            }
        }
    }

    void visit(Generator* generator) override {
        if (generator->external() || generator->is_stub()) return;
        if (!run_pass_) return;
        Port* port;
        if (generator->has_port(reset_name_)) {
            port = generator->get_port(reset_name_).get();
            if (port->port_type() != PortType::Reset) {
                port->set_port_type(PortType::Reset);
            }
        } else {
            // create a synchronous reset port
            port = &generator->port(PortDirection::In, reset_name_, 1, PortType::Reset);
        }
        // look through each sequential block
        auto stmts_count = generator->stmts_count();
        for (uint64_t i = 0; i < stmts_count; i++) {
            auto stmt = generator->get_stmt(i);
            if (stmt->type() == StatementType::Block) {
                auto blk = stmt->as<StmtBlock>();
                if (blk->block_type() == StatementBlockType::Sequential) {
                    auto seq = blk->as<SequentialStmtBlock>();
                    inject_reset_logic(seq.get(), port);
                }
            }
        }

        // wire the children. we do in this order since this pass is run in parallel from bottom
        // up
        for (auto const& child : generator->get_child_generators()) {
            if (child->has_port(reset_name_)) {
                auto child_port = child->get_port(reset_name_);
                auto sources = child_port->sources();
                if (sources.size() > 1) continue;
                if (sources.size() == 1) {
                    auto* right = (*sources.begin())->right();
                    if (right->type() == VarType::ConstValue) {
                        child_port->clear_sources(true);
                    }
                }
                generator->wire(*child_port, *port);
            }
        }
    }

private:
    bool run_pass_ = false;
    bool over_clk_en_ = false;
    std::string reset_name_;
    const std::string sync_reset_name = "sync-reset";

    void inject_reset_logic(SequentialStmtBlock* block, Port* port) const {
        // only inject when there is a async reset logic
        auto stmts_count = block->size();
        if (stmts_count != 1) return;
        auto stmt = block->get_stmt(0);
        if (stmt->type() != StatementType::If) return;
        auto if_ = stmt->as<IfStmt>();
        auto const& cond = if_->predicate();
        // if it doesn't have async reset logic, or it already has sync reset logic
        // quit
        if (!has_port_type(cond.get(), PortType::AsyncReset) ||
            has_port_type(cond.get(), PortType::Reset))
            return;
        auto* reset_stmt = if_->then_body().get();
        // okay we have reset now. now we need to detect if it has clock enable
        // logic or not
        // we need to detect the clock enable logic and make sure that the ordering is what
        // specified in the
        auto else_body = if_->else_body();
        // detect if clock enable have been in place
        if (else_body->size() == 1) {
            auto then_stmt = else_body->get_stmt(0);
            if (then_stmt->type() == StatementType::If) {
                auto if_then = then_stmt->as<IfStmt>();
                auto target = if_then->predicate();
                if (has_port_type(target.get(), PortType::ClockEnable) && !over_clk_en_) {
                    // could be the case that it already has a reset
                    if (!if_then->then_body()->empty() &&
                        if_then->then_body()->get_stmt(0)->type() == StatementType::If) {
                        auto if_2 = if_then->then_body()->get_stmt(0)->as<IfStmt>();
                        // user already put it there
                        if (has_port_type(if_2->predicate().get(), PortType::Reset)) return;
                    }
                    // insert inside the clock enable body
                    auto body = if_then->then_body()->clone()->as<ScopedStmtBlock>();
                    // need to duplicate the logic in reset
                    auto sync_reset = create_if_stmt_wrapper(reset_stmt, *port, true);
                    sync_reset->set_else(body);
                    if_then->then_body()->clear();
                    if_then->add_then_stmt(sync_reset);
                    return;
                } else if (has_port_type(target.get(), PortType::Reset)) {
                    // already has a sync reset
                    return;
                }
            }
        }
        auto sync_reset = create_if_stmt_wrapper(reset_stmt, *port, true);
        auto body = else_body->clone()->as<ScopedStmtBlock>();
        sync_reset->set_else(body);
        else_body->clear();
        else_body->add_stmt(sync_reset);
    }
};

void auto_insert_sync_reset(Generator* top) {
    InsertSyncReset visitor(top);
    visitor.visit_generator_root_p(top);
}

class RemoveEmptyBlockVisitor : public IRVisitor {
public:
    void visit(Generator* top) override {
        auto stmt_count = top->stmts_count();
        std::vector<std::shared_ptr<Stmt>> stmts_to_remove;
        for (uint64_t i = 0; i < stmt_count; i++) {
            auto stmt = top->get_stmt(i);
            if (!dispatch_node(stmt)) stmts_to_remove.emplace_back(stmt);
        }
        for (auto const& stmt : stmts_to_remove) {
            top->remove_stmt(stmt);
        }
    }

private:
    std::shared_ptr<IfStmt> process(std::shared_ptr<IfStmt> stmt) {
        auto then_ = stmt->then_body();
        auto then_body = process(then_);
        auto else_body = process(stmt->else_body());
        if (!then_body) {
            // then is empty
            if (else_body->empty()) {
                return nullptr;
            } else {
                // invert the condition and make else then
                auto cond = stmt->predicate();
                auto& new_cond = ~(*cond);
                stmt->set_predicate(new_cond.shared_from_this());
                stmt->set_then(else_body->as<ScopedStmtBlock>());
                stmt->set_else(std::make_shared<ScopedStmtBlock>());
                return stmt;
            }
        }
        stmt->set_then(then_body->as<ScopedStmtBlock>());
        return stmt;
    }

    std::shared_ptr<StmtBlock> process(std::shared_ptr<StmtBlock> stmt) {
        auto stmt_count = stmt->size();
        std::vector<std::shared_ptr<Stmt>> stmts_to_remove;
        for (uint64_t i = 0; i < stmt_count; i++) {
            auto st = stmt->get_stmt(i);
            auto r = dispatch_node(st);
            if (!r) {
                stmts_to_remove.emplace_back(st);
                continue;
            }
            stmt->set_child(i, r);
        }
        for (auto const& st : stmts_to_remove) {
            stmt->remove_stmt(st);
        }
        if (stmt->empty())
            return nullptr;
        else
            return stmt;
    }

    std::shared_ptr<SwitchStmt> process(std::shared_ptr<SwitchStmt> stmt) {
        std::map<std::shared_ptr<Const>, std::shared_ptr<ScopedStmtBlock>> new_body;
        auto const& body = stmt->body();
        for (const auto& [cond, block] : body) {
            auto r = process(block);
            if (r) {
                new_body.emplace(cond, r->as<ScopedStmtBlock>());
            }
        }
        if (new_body.empty()) return nullptr;
        stmt->set_body(new_body);
        return stmt;
    }

    std::shared_ptr<Stmt> dispatch_node(std::shared_ptr<Stmt> stmt) {
        if (stmt->type() == StatementType::If) {
            return process(std::static_pointer_cast<IfStmt>(stmt));
        } else if (stmt->type() == StatementType::Switch) {
            return process(std::static_pointer_cast<SwitchStmt>(stmt));
        } else if (stmt->type() == StatementType::Block) {
            return process(std::static_pointer_cast<ScopedStmtBlock>(stmt));
        } else {
            return stmt;
        }
    }
};

void remove_empty_block(Generator* top) {
    RemoveEmptyBlockVisitor visitor;
    visitor.visit_root(top);
}

class MergeConstPortVisitor : public IRVisitor {
    void visit(Generator* generator) override {
        // scan each var that's one source and one sink, where the source is a constant
        // and the sink is a child generator instance input port
        auto const vars = generator->get_vars();
        std::set<std::string> vars_to_remove;
        std::set<std::shared_ptr<Stmt>> stmts_to_remove;

        for (auto const& var_name : vars) {
            auto const& var = generator->get_var(var_name);
            if (var->type() == VarType::Base && var->sources().size() == 1 &&
                var->sinks().size() == 1) {
                auto source_stmt = *(var->sources().begin());
                auto sink_stmt = *(var->sinks().begin());
                auto* source_from = source_stmt->right();
                auto* sink_to = sink_stmt->left();
                if (source_from->type() == VarType::ConstValue &&
                    sink_to->type() == VarType::PortIO &&
                    sink_to->generator()->parent() == generator) {
                    sink_to->clear_sources(false);
                    generator->add_stmt(sink_to->assign(*source_from, AssignmentType::Blocking));
                    var->remove_sink(sink_stmt);
                    var->remove_source(source_stmt);
                    stmts_to_remove.emplace(sink_stmt);
                    stmts_to_remove.emplace(source_stmt);
                    vars_to_remove.emplace(var_name);
                }
            }
        }

        for (auto const& var_name : vars_to_remove) {
            generator->remove_var(var_name);
        }
        for (auto const& stmt : stmts_to_remove) {
            generator->remove_stmt(stmt);
        }
    }
};

void merge_const_port_assignment(Generator* top) {
    MergeConstPortVisitor visitor;
    visitor.visit_generator_root_p(top);
}

class VarUnusedVisitor : public IRVisitor {
public:
    void visit(Generator* generator) override {
        std::set<std::string> vars_to_remove;
        auto vars = generator->vars();
        for (auto const& [var_name, var] : vars) {
            if (var->type() != VarType::Base || var->is_interface()) continue;
            if (var->sinks().empty()) {
                if (var->sources().empty() && !var->is_interface()) {
                    vars_to_remove.emplace(var_name);
                } else {
                    // print out warnings
                    error_mutex_.lock();
                    std::cerr << "Variable: " << var->to_string() << " has no sink" << std::endl;
                    print_ast_node(var.get());
                    error_mutex_.unlock();
                }
            }
        }

        // remove unused vars
        for (auto const& var_name : vars_to_remove) {
            generator->remove_var(var_name);
        }
    }

private:
    std::mutex error_mutex_;
};

void remove_unused_vars(Generator* top) {
    VarUnusedVisitor visitor;
    visitor.visit_generator_root_p(top);
}

class UnusedTopBlockVisitor : public IRVisitor {
    void visit(Generator* generator) override {
        std::set<std::shared_ptr<Stmt>> blocks_to_remove = {};
        uint64_t stmt_count = generator->stmts_count();
        for (uint64_t i = 0; i < stmt_count; i++) {
            auto stmt = generator->get_stmt(i);
            if (stmt->type() == StatementType::Block) {
                auto* block = dynamic_cast<StmtBlock*>(stmt.get());
                if (block->empty()) blocks_to_remove.emplace(stmt);
            }
        }

        for (auto const& stmt : blocks_to_remove) {
            generator->remove_stmt(stmt);
        }
    }
};

void remove_unused_stmts(Generator* top) {
    // for now we'll just remove the top level unused blocks
    // ideally this should be done through multiple rounds to avoid circular reference,
    // removed dead stmts and other problems. It should also remove all the other empty statements
    UnusedTopBlockVisitor visitor;
    visitor.visit_generator_root(top);
}

class DeadCodeVarElimination : public IRVisitor {
    // this pass only removes dead variables in the parent generator
public:
    void visit(Generator* generator) override {
        bool changed = true;

        while (changed) {
            changed = false;
            const auto& var_names = generator->get_vars();
            for (auto const& var_name : var_names) {
                auto const& var = generator->get_var(var_name);
                if (var->type() != VarType::Base) continue;
                if (var->sinks().empty()) {
                    // remove all the sources
                    remove_var(var.get());
                    changed = true;
                    break;
                }
            }
        }

        // because we run child first, the parent's content get cleared out
        // nicely before this pass runs on parent
        clear_out_ports(generator);
    }

private:
    static void clear_out_ports(Generator* generator) {
        // we don't deal with top level ports, since it changes
        // interface
        if (!generator->parent_generator()) return;
        auto const& port_names = generator->get_port_names();
        std::vector<std::string> ports_to_remove;
        for (auto const& port_name : port_names) {
            auto const& p = generator->get_port(port_name);
            if (p->port_direction() == PortDirection::In) {
                if (p->sinks().empty()) {
                    ports_to_remove.emplace_back(port_name);
                }
            } else if (p->port_direction() == PortDirection::Out) {
                if (p->sources().empty()) {
                    ports_to_remove.emplace_back(port_name);
                }
            }
        }

        auto* parent = generator->parent_generator();
        for (auto const& port_name : ports_to_remove) {
            // need to un-wire the parent
            auto const& port = generator->get_port(port_name);
            remove_var(port.get());
            generator->remove_port(port_name);
        }
    }

    static void remove_var(Var* var) {
        auto* generator = var->generator();

        auto sources = std::unordered_set<std::shared_ptr<AssignStmt>>(var->sources());
        for (auto const& stmt : sources) {
            auto* right = stmt->right();
            right->remove_sink(stmt);
            var->remove_source(stmt);
            stmt->remove_from_parent();
        }

        auto sinks = std::unordered_set<std::shared_ptr<AssignStmt>>(var->sinks());
        for (auto const& stmt : sinks) {
            auto* left = stmt->left();
            left->remove_source(stmt);
            var->remove_sink(stmt);
            stmt->remove_from_parent();
        }

        generator->remove_var(var->name);
    }
};

class DeadCodeInstanceElimination : public IRVisitor {
    // this pass eliminates empty instance
public:
    void visit(Generator* generator) override {
        auto const& children = generator->get_child_generators();
        std::vector<std::shared_ptr<Generator>> remove_set;
        for (auto const& child : children) {
            if (child->get_port_names().empty()) {
                remove_set.emplace_back(child);
            }
        }
        for (auto const& child : remove_set) {
            generator->remove_child_generator(child);
        }
    }
};

void dead_code_elimination(Generator* top) {
    {
        DeadCodeVarElimination visitor;
        visitor.visit_generator_root_p(top);
    }
    {
        DeadCodeInstanceElimination visitor;
        visitor.visit_generator_root_p(top);
    }

    // clean up empty stmt blocks
    remove_empty_block(top);
}

}  // namespace kratos