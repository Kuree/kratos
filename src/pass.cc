#include "pass.hh"
#include <algorithm>
#include <iostream>
#include <sstream>
#include "codegen.hh"
#include "except.hh"
#include "fmt/format.h"
#include "generator.hh"
#include "port.hh"
#include "util.hh"

using fmt::format;
using std::runtime_error;

class AssignmentTypeVisitor : public ASTVisitor {
public:
    explicit AssignmentTypeVisitor(AssignmentType type, bool check_type = true)
        : ASTVisitor(), type_(type), check_type_(check_type) {}
    void visit(AssignStmt* stmt) override {
        if (stmt->assign_type() == AssignmentType::Undefined) {
            stmt->set_assign_type(type_);
        } else if (check_type_ && stmt->assign_type() != type_) {
            throw ::runtime_error(::format("mismatch in assignment type. should be {0}, got {1}",
                                           assign_type_to_str(type_),
                                           assign_type_to_str(stmt->assign_type())));
        }
    }

private:
    AssignmentType type_;
    bool check_type_;
};

class AssignmentTypeBlockVisitor : public ASTVisitor {
    void visit(CombinationalStmtBlock* block) override {
        AssignmentTypeVisitor visitor(AssignmentType::Blocking, true);
        visitor.visit_root(block->ast_node());
    }
    void visit(SequentialStmtBlock* block) override {
        AssignmentTypeVisitor visitor(AssignmentType::NonBlocking, true);
        visitor.visit_root(block->ast_node());
    }
};

void fix_assignment_type(Generator* top) {
    // first we fix all the block assignment
    AssignmentTypeBlockVisitor visitor;
    visitor.visit_root(top);
    visitor.visit_generator_root(top);

    // then we assign any existing assignment as blocking assignment
    AssignmentTypeVisitor final_visitor(AssignmentType::Blocking, false);
    final_visitor.visit_root(top->ast_node());
}

class VerifyAssignmentVisitor : public ASTVisitor {
public:
    explicit VerifyAssignmentVisitor(Generator* generator) : generator_(generator) {}

    void visit(AssignStmt* stmt) override {
        const auto left = stmt->left();
        auto right = stmt->right();
        // if the right hand side is a const and it's safe to do so, we will let it happen
        if (left->width != right->width) {
            if (right->type() == VarType::ConstValue) {
                auto old_value = right->as<Const>();
                try {
                    auto& new_const =
                        generator_->constant(old_value->value(), left->width, old_value->is_signed);
                    stmt->set_right(new_const.shared_from_this());
                    right = new_const.shared_from_this();
                } catch (::runtime_error&) {
                    std::cerr << "Failed to convert constants. Expect an exception" << std::endl;
                }
            }
        }
        if (left->width != right->width)
            throw StmtException(
                ::format("assignment width doesn't match. left ({0}): {1} right ({2}): {3}",
                         left->to_string(), left->width, right->to_string(), right->width),
                {stmt});
        if (left->is_signed != right->is_signed)
            throw StmtException(
                ::format("assignment sign doesn't match. left ({0}): {1} right ({2}): {3}",
                         left->to_string(), left->is_signed, right->to_string(), right->is_signed),
                {stmt});
    }

    void visit(Generator* generator) override {
        auto vars = generator->get_all_var_names();
        for (auto const& var_name : vars) {
            auto var = generator->get_var(var_name);
            check_var(var.get());
        }
    }

private:
    Generator* generator_;

    void inline static check_var(Var* var) {
        bool is_top_level = false;
        auto sources = var->sources();
        for (auto const& stmt : sources) {
            if (stmt->parent()->ast_node_kind() == ASTNodeKind::GeneratorKind) {
                is_top_level = true;
                break;
            }
        }

        // second pass the check all the assignments
        bool has_error = false;
        if (is_top_level) {
            for (auto const& stmt : sources) {
                if (stmt->parent()->ast_node_kind() != ASTNodeKind::GeneratorKind) {
                    has_error = true;
                    break;
                }
            }
        }

        if (has_error) {
            std::vector<Stmt*> stmt_list;
            // prepare the error
            for (auto const& stmt : sources) {
                stmt_list.emplace_back(stmt.get());
            }
            throw StmtException(::format("{0} has wire assignment yet is also used in always block",
                                         var->to_string()),
                                stmt_list);
        }
    }
};

void verify_assignments(Generator* top) {
    // verify the assignment width match, and sign as well
    VerifyAssignmentVisitor visitor(top);
    visitor.visit_root(top);
}

class VarAccumulationVisitor : public ASTVisitor {
public:
    VarAccumulationVisitor() : ASTVisitor(), vars() {}
    void visit(Var* var) override {
        if (var->type() == VarType ::Base) vars.emplace(var->name);
    }
    std::set<std::string> vars;
};

void remove_unused_vars(Generator* top) {
    // get a set of all variables
    std::set<std::string> var_names;
    for (auto const& [var_name, var] : top->vars()) {
        if (var->type() == VarType::Base) var_names.emplace(var_name);
    }
    // visit each assignment to see if we have used it or not
    VarAccumulationVisitor visitor;
    visitor.visit_root(top);

    // result set
    std::set<std::string> diff_set;
    std::set_difference(var_names.begin(), var_names.end(), visitor.vars.begin(),
                        visitor.vars.end(), std::inserter(diff_set, diff_set.end()));
    for (const auto& var_name : diff_set) {
        top->remove_var(var_name);
    }
}

class GeneratorConnectivityVisitor : public ASTVisitor {
public:
    GeneratorConnectivityVisitor() : is_top_level_(true) {}
    void visit(Generator* generator) override {
        // skip if it's an external module or stub module
        if (generator->external() || generator->is_stub()) return;
        const auto& port_names = generator->get_port_names();
        for (const auto& port_name : port_names) {
            auto const& port = generator->get_port(port_name);

            // based on whether it's an input or output
            // for inputs, if it's not top generator, we need to check if
            // something is driving it
            if (port->port_direction() == PortDirection::In) {
                if (is_top_level_) continue;
            }

            bool has_error = true;
            std::unordered_set<uint32_t> bits;
            bits.reserve(port->width);
            if (!port->sources().empty()) {
                // it has been assigned. need to compute all the slices
                auto sources = port->sources();
                for (auto& stmt : sources) {
                    auto src = stmt->right();
                    if (src->type() == VarType::Slice) {
                        auto ptr = src->as<VarSlice>();
                        auto low = ptr->low;
                        auto high = ptr->high;
                        for (uint32_t i = low; i <= high; i++) {
                            bits.emplace(i);
                        }
                    } else {
                        has_error = false;
                        for (uint32_t i = 0; i < port->width; i++) bits.emplace(i);
                        break;
                    }
                }
            }
            if (!has_error && bits.size() != port->width) has_error = true;

            if (has_error) {
                std::vector<Stmt*> stmt_list;
                for (auto const& stmt : port->sources()) {
                    stmt_list.emplace_back(stmt.get());
                }
                for (uint32_t i = 0; i < port->width; i++) {
                    if (bits.find(i) == bits.end()) {
                        throw StmtException(
                            ::format("{0}[{1}] is a floating net. Please check your connections",
                                     port_name, i),
                            stmt_list);
                    }
                }
            }
        }

        is_top_level_ = false;
    }

private:
    bool is_top_level_;
};

void verify_generator_connectivity(Generator* top) {
    GeneratorConnectivityVisitor visitor;
    visitor.visit_generator_root(top);
}

class ModuleInstantiationVisitor : public ASTVisitor {
public:
    void visit(Generator* generator) override {
        for (auto& child : generator->get_child_generators()) {
            // create instantiation statement
            auto stmt = std::make_shared<ModuleInstantiationStmt>(child.get(), generator);
            if (generator->debug) {
                // get the debug info from the add_generator, if possible
                auto debug_info = generator->children_debug();
                if (debug_info.find(child) != debug_info.end()) {
                    auto info = debug_info.at(child);
                    stmt->fn_name_ln.emplace_back(info);
                }
                stmt->fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
            }
            generator->add_stmt(stmt);
        }
    }
};

void create_module_instantiation(Generator* top) {
    ModuleInstantiationVisitor visitor;
    visitor.visit_generator_root(top);
}

class UniqueGeneratorVisitor : public ASTVisitor {
public:
    std::map<std::string, Generator*> generator_map;

    void visit(Generator* generator) override {
        if (generator_map.find(generator->name) != generator_map.end()) return;
        // a unique one
        if (!generator->external()) generator_map.emplace(generator->name, generator);
    }
};

std::map<std::string, std::string> generate_verilog(Generator* top) {
    // this pass assumes that all the generators has been uniquified
    std::map<std::string, std::string> result;
    std::map<std::string, DebugInfo> debug_info;
    // first get all the unique generators
    UniqueGeneratorVisitor unique_visitor;
    unique_visitor.visit_generator_root(top);
    for (auto& [module_name, module_gen] : unique_visitor.generator_map) {
        SystemVerilogCodeGen codegen(module_gen);
        result.emplace(module_name, codegen.str());
    }
    return result;
}

void hash_generators(Generator* top, HashStrategy strategy) {
    // this is a helper function
    hash_generators_context(top->context(), top, strategy);
}

void uniquify_generators(Generator* top) {
    // we assume users has run the hash_generators function
    Context* context = top->context();
    auto const& names = context->get_generator_names();
    for (auto const& name : names) {
        const auto module_instances = context->get_generators_by_name(name);
        // notice that since it is a set copied by value, it is fine to iterate through it
        if (module_instances.size() == 1)
            // only one module. we are good
            continue;
        // there is almost little change that the hash value will be 0
        // but still, there is a tiny chance...
        uint64_t hash = 0;
        for (auto& instance : module_instances) {
            auto ptr = instance.get();
            if (context->has_hash(ptr)) {
                if (hash == 0) {
                    hash = context->get_hash(ptr);
                } else if (context->get_hash(ptr) != hash) {
                    // we need to uniquify it
                    // this is a naive way
                    uint32_t count = 0;
                    while (true) {
                        const std::string new_name = ::format("{0}_unq{1}", name, count++);
                        if (!context->generator_name_exists(new_name)) {
                            context->change_generator_name(ptr, new_name);
                            break;
                        }
                    }
                }
            } else {
                throw ::runtime_error(
                    ::format("{0} ({1}) doesn't have hash", ptr->instance_name, ptr->name));
            }
        }
    }
}

class ModuleInstanceVisitor : public ASTVisitor {
public:
    void visit(Generator* generator) override {
        std::unordered_set<std::string> names;
        auto children = generator->get_child_generators();
        for (auto& child : children) {
            std::string instance_name;
            if (child->instance_name == child->name) {
                // renamed to inst
                instance_name = ::format("{0}_inst", child->name);
            } else {
                instance_name = child->instance_name;
            }
            if (names.find(instance_name) == names.end()) {
                // we are good
                child->instance_name = instance_name;
            } else {
                uint32_t count = 0;
                while (true) {
                    std::string new_name = ::format("{0}{1}", instance_name, count++);
                    if (names.find(new_name) == names.end()) {
                        // we are good
                        child->instance_name = new_name;
                        break;
                    }
                }
            }
            // add it to the names list
            names.emplace(child->instance_name);
        }
    }
};

void uniquify_module_instances(Generator* top) {
    ModuleInstanceVisitor visitor;
    visitor.visit_generator_root(top);
}

class GeneratorPortVisitor : public ASTVisitor {
public:
    void visit(Generator* generator) override {
        if (!generator->parent()) {
            // this is top level module, no need to worry about it
            return;
        }
        auto const& port_names = generator->get_port_names();

        for (auto const& port_name : port_names) {
            auto port = generator->get_port(port_name);
            auto const port_direction = port->port_direction();
            if (port_direction == PortDirection::In) {
                const auto& sources = port->sources();
                // unless it's driven by a single var or port, we need to duplicate
                // the variable
                if (sources.size() == 1) {
                    const auto& stmt = *sources.begin();
                    if (stmt->left() == port) {
                        // the sink has to be it self
                        auto src = stmt->right();
                        if (src->type() == VarType::Base || src->type() == VarType::ConstValue ||
                            src->type() == VarType::Parameter ||
                            (src->type() == VarType::PortIO &&
                             src->parent() == generator->parent())) {
                            continue;
                        }
                    }
                }
                // create a new variable
                auto ast_parent = generator->parent();
                if (!ast_parent)
                    throw ::runtime_error(::format(
                        "{0}'s parent is empty but it's not a top module", generator->name));
                auto parent = reinterpret_cast<Generator*>(ast_parent);
                auto new_name =
                    parent->get_unique_variable_name(generator->instance_name, port_name);
                auto& var = parent->var(new_name, port->width, port->is_signed);
                if (parent->debug) {
                    // need to copy over the changes over
                    var.fn_name_ln = std::vector<std::pair<std::string, uint32_t>>(
                        port->fn_name_ln.begin(), port->fn_name_ln.end());
                    var.fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
                }
                // replace all the sources
                Var::move_src_to(port.get(), &var, parent, true);
            } else if (port_direction == PortDirection::Out) {
                // same logic as the port dir in
                // if we're connected to a base variable, we are good
                const auto& sinks = port->sinks();
                if (sinks.empty()) {
                    continue;
                }
                // special case where if the sink is parent's port, this is fine
                if (sinks.size() == 1) {
                    auto stmt = *(sinks.begin());
                    if (stmt->left()->type() == VarType::PortIO &&
                        stmt->left()->generator == generator->parent() && stmt->right() == port) {
                        continue;
                    }
                }
                // create a new variable
                auto ast_parent = generator->parent();
                if (!ast_parent)
                    throw ::runtime_error(::format(
                        "{0}'s parent is empty but it's not a top module", generator->name));
                auto parent = reinterpret_cast<Generator*>(ast_parent);
                auto new_name =
                    parent->get_unique_variable_name(generator->instance_name, port_name);
                auto& var = parent->var(new_name, port->width, port->is_signed);
                if (parent->debug) {
                    // need to copy over the changes over
                    var.fn_name_ln = std::vector<std::pair<std::string, uint32_t>>(
                        port->fn_name_ln.begin(), port->fn_name_ln.end());
                    var.fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
                }
                // replace all the sources
                Var::move_sink_to(port.get(), &var, parent, true);
            } else {
                throw ::runtime_error("Not implement yet");
            }
        }
    }
};

void decouple_generator_ports(Generator* top) {
    GeneratorPortVisitor visitor;
    visitor.visit_generator_root(top);
}

class StubGeneratorVisitor : public ASTVisitor {
public:
    void visit(Generator* generator) override {
        if (!generator->is_stub()) return;
        // to be a stub, there shouldn't be any extra variables
        if (generator->stmts_count() > 0) {
            throw ::runtime_error(::format("{0} is marked as a stub but contains statements"));
        }

        // has to be the exact same number of ports and vars, otherwise it means there are
        // some variables being declared
        auto vars = generator->get_vars();
        auto ports = generator->get_port_names();
        if (!vars.empty()) {
            throw ::runtime_error(
                fmt::format("{0} is declared as stub but has declared variables", generator->name));
        }

        for (auto const& port_name : ports) {
            auto port = generator->get_port(port_name);
            if (port->port_direction() == PortDirection::In) {
                if (!port->sinks().empty())
                    throw ::runtime_error(
                        fmt::format("{0}.{1} is driving a net, but {0} is declared as a stub",
                                    generator->name, port_name));
            } else {
                if (!port->sources().empty())
                    throw ::runtime_error(
                        fmt::format("{0}.{1} is driven by a net, but {0} is declared as a stub",
                                    generator->name, port_name));
                generator->add_stmt(
                    port->assign(generator->constant(0, port->width)).shared_from_this());
            }
        }
    }
};

void zero_out_stubs(Generator* top) {
    StubGeneratorVisitor visitor;
    visitor.visit_generator_root(top);
}

class MixedAssignmentVisitor : public ASTVisitor {
public:
    void visit(Generator* generator) override {
        auto const vars = generator->get_vars();
        auto const ports = generator->get_port_names();
        for (const auto& var_name : vars) {
            checkout_assignment(generator, var_name);
        }
        for (const auto& port_name : ports) {
            checkout_assignment(generator, port_name);
        }
    }
    void checkout_assignment(Generator* generator, const std::string& name) const {
        auto const& var = generator->get_var(name);
        AssignmentType type = Undefined;
        for (auto const& stmt : var->sources()) {
            if (type == Undefined)
                type = stmt->assign_type();
            else if (type != stmt->assign_type()) {
                std::vector<Stmt*> stmt_list;
                stmt_list.reserve(var->sources().size());
                for (const auto& st : var->sources()) stmt_list.emplace_back(st.get());
                throw StmtException(::format("Mixed assignment detected for variable {0}.{1}",
                                             generator->name, name),
                                    stmt_list);
            }
        }
    }
};

void check_mixed_assignment(Generator* top) {
    MixedAssignmentVisitor visitor;
    visitor.visit_generator_root(top);
}

class TransformIfCase : public ASTVisitor {
public:
    void visit(CombinationalStmtBlock* stmts) override {
        for (uint32_t i = 0; i < stmts->child_count(); i++) {
            auto stmt = reinterpret_cast<Stmt*>(stmts->get_child(i));
            Var* target = nullptr;
            std::unordered_set<std::shared_ptr<Stmt>> if_stmts;
            if (has_target_if(stmt, target, if_stmts)) {
                auto switch_stmt = change_if_to_switch(stmt->as<IfStmt>(), if_stmts);
                stmts->set_child(i, switch_stmt);
            }
        }
    }
    void visit(SequentialStmtBlock*) override {}

private:
    bool static has_target_if(Stmt* stmt, Var*& var,
                              std::unordered_set<std::shared_ptr<Stmt>>& if_stmts) {
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
            var = expr->left.get();
        } else {
            if (var != expr->left.get()) return false;
        }
        if ((expr->right->type() != VarType::ConstValue) &&
            (expr->right->type() != VarType::Parameter))
            return false;
        if (if_->else_body().size() > 1) return false;

        if_stmts.emplace(if_);
        if (if_->else_body().empty()) {
            return true;
        } else if (if_->then_body().size() > 1) {
            return if_stmts.size() > 1;
        } else {
            return has_target_if(if_->else_body()[0].get(), var, if_stmts);
        }
    }

    std::shared_ptr<SwitchStmt> static change_if_to_switch(
        std::shared_ptr<IfStmt> stmt, const std::unordered_set<std::shared_ptr<Stmt>>& if_stmts) {
        auto expr = stmt->predicate()->as<Expr>();
        // we assume that this is a valid case (see has_target_if)
        auto target = expr->left;
        std::shared_ptr<SwitchStmt> switch_ = std::make_shared<SwitchStmt>(target);
        if (target->generator->debug) {
            switch_->fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
        }

        while (if_stmts.find(stmt) != if_stmts.end()) {
            auto condition = expr->right->as<Const>();
            switch_->add_switch_case(condition, stmt->then_body());
            if (!stmt->else_body().empty() &&
                if_stmts.find(stmt->else_body()[0]) == if_stmts.end()) {
                // we have reached the end
                // add default statement
                switch_->add_switch_case(nullptr, stmt->else_body());
                break;
            } else if (!stmt->else_body().empty()) {
                // switch to the else case
                stmt = stmt->else_body()[0]->as<IfStmt>();
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

class VarFanOutVisitor : public ASTVisitor {
public:
    void visit(Generator* generator) override {
        auto var_names = generator->get_all_var_names();
        for (auto const& var_name : var_names) {
            auto var = generator->get_var(var_name);
            std::vector<std::pair<std::shared_ptr<Var>, std::shared_ptr<AssignStmt>>> chain;
            compute_assign_chain(var, chain);
            if (chain.size() <= 2) continue;  // nothing to be done

            std::vector<std::pair<std::string, uint32_t>> debug_info;

            for (uint32_t i = 0; i < chain.size() - 1; i++) {
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
                auto& assign = dst->assign(var, AssignmentType::Blocking);
                auto stmt = assign.shared_from_this();
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
            if (stmt->parent()->ast_node_kind() == ASTNodeKind::GeneratorKind) {
                auto sink_var = stmt->left();
                if (sink_var->parent() != var->parent()) {
                    // not the same parent
                    return;
                }
                queue.emplace_back(std::make_pair(var, stmt));
                compute_assign_chain(sink_var, queue);
            }
        } else {
            queue.emplace_back(std::make_pair(var, nullptr));
        }
    }
};

void remove_fanout_one_wires(Generator* top) {
    VarFanOutVisitor visitor;
    visitor.visit_generator_root(top);
}

class RemovePassThroughVisitor : public ASTVisitor {
public:
    void visit(Generator* generator) override {
        const auto& children = generator->get_child_generators();
        std::set<std::shared_ptr<Generator>> child_to_remove;
        for (auto const& child : children) {
            if (is_pass_through(child.get())) {
                // need to remove it
                child_to_remove.emplace(child);
            }
        }

        for (auto const& child : child_to_remove) {
            // we move the src and sinks around
            const auto& port_names = generator->get_port_names();
            for (auto const& port_name : port_names) {
                auto port = child->get_port(port_name);
                if (port->port_direction() == PortDirection::In) {
                    // move the src to whatever it's connected to
                    // basically compress the module into a variable
                    // we will let the later downstream passes to remove the extra wiring
                    auto next_port = (*(port->sinks().begin()))->left();
                    auto var_name = generator->get_unique_variable_name(generator->name, port_name);
                    auto& new_var = generator->var(var_name, port->width, port->is_signed);
                    if (generator->debug) {
                        // need to copy the changes over
                        new_var.fn_name_ln = std::vector<std::pair<std::string, uint32_t>>(
                            child->fn_name_ln.begin(), child->fn_name_ln.end());
                        new_var.fn_name_ln.emplace_back(__FILE__, __LINE__);
                    }
                    Var::move_src_to(port.get(), &new_var, generator, false);
                    // move the sinks over
                    Var::move_sink_to(next_port.get(), &new_var, generator, false);
                }
            }
            // remove it from the generator children
            generator->remove_child_generator(child->shared_from_this());
        }
    }

private:
    bool static is_pass_through(Generator* generator) {
        const auto vars = generator->get_vars();
        // has to be empty
        if (!vars.empty()) return false;
        // has to have exact number of assignments as ports
        // ports has to be an even number, i.e. one in to one out
        // maybe we can relax this restriction later
        auto const port_names = generator->get_port_names();
        if (port_names.size() % 2) return false;
        if (generator->stmts_count() != port_names.size() / 2) return false;

        for (const auto& port_name : port_names) {
            auto const port = generator->get_port(port_name);
            if (port->port_direction() == PortDirection::In) {
                auto sinks = port->sinks();
                if (sinks.size() != 1) return false;
            } else {
                auto sources = port->sources();
                if (sources.size() != 1) return false;
                // maybe some add stuff
                auto stmt = *(sources.begin());
                auto src = stmt->right();
                if (src->type() != VarType::PortIO) return false;
            }
        }
        return true;
    }
};

void remove_pass_through_modules(Generator* top) {
    RemovePassThroughVisitor visitor;
    visitor.visit_generator_root(top);
}

// this is only for visiting the vars and assignments in the current generator
class DebugInfoVisitor : public ASTVisitor {
public:
    void visit(Var* var) override { add_info(var); }

    void inline visit(AssignStmt* stmt) override { add_info(stmt); }

    void visit(Port* var) override { add_info(var); }

    void visit(SwitchStmt* stmt) override { add_info(stmt); }

    void inline visit(SequentialStmtBlock* stmt) override { add_info(stmt); }

    void inline visit(CombinationalStmtBlock* stmt) override { add_info(stmt); }

    void inline visit(ModuleInstantiationStmt* stmt) override { add_info(stmt); }

    std::map<uint32_t, std::vector<std::pair<std::string, uint32_t>>> result;

private:
    void inline add_info(Stmt* stmt) {
        if (!stmt->fn_name_ln.empty() && stmt->verilog_ln != 0) {
            result.emplace(stmt->verilog_ln, stmt->fn_name_ln);
        }
    }

    void inline add_info(Var* var) {
        if (!var->fn_name_ln.empty() && var->verilog_ln != 0 &&
            result.find(var->verilog_ln) == result.end()) {
            result.emplace(var->verilog_ln, var->fn_name_ln);
        }
    }
};

class GeneratorDebugVisitor : public ASTVisitor {
public:
    void visit(Generator* generator) override {
        if (result.find(generator->name) != result.end()) return;
        if (!generator->fn_name_ln.empty()) {
            DebugInfoVisitor visitor;
            visitor.result.emplace(1, generator->fn_name_ln);
            visitor.visit_content(generator);
            result.emplace(generator->name, visitor.result);
        }
    }

    std::map<std::string, std::map<uint32_t, std::vector<std::pair<std::string, uint32_t>>>> result;
};

std::map<std::string, std::map<uint32_t, std::vector<std::pair<std::string, uint32_t>>>>
extract_debug_info(Generator* top) {
    GeneratorDebugVisitor visitor;
    visitor.visit_generator_root(top);
    return visitor.result;
}

class PortPackedVisitor : public ASTVisitor {
public:
    void visit(Generator* generator) override {
        auto const port_names = generator->get_port_names();
        for (auto const& port_name : port_names) {
            auto port = generator->get_port(port_name);
            if (port->is_packed()) {
                auto ptr = port->as<PortPacked>();
                auto const port_struct = ptr->packed_struct();
                if (structs.find(port_struct.struct_name) != structs.end()) {
                    // do some checking
                    auto struct_ = structs.at(port_struct.struct_name);
                    if (struct_.attributes.size() != port_struct.attributes.size())
                        throw VarException(::format("redefinition of different packed struct {0}",
                                                    port_struct.struct_name),
                                           {port.get(), struct_ports_.at(port_struct.struct_name)});
                    for (uint32_t i = 0; i < port_struct.attributes.size(); i++) {
                        auto const& [name1, width1, signed_1] = struct_.attributes[i];
                        auto const& [name2, width2, signed_2] = port_struct.attributes[i];
                        if (name1 != name2 || width1 != width2 || signed_1 != signed_2)
                            throw VarException(
                                ::format("redefinition of different packed struct {0}",
                                         port_struct.struct_name),
                                {port.get(), struct_ports_.at(port_struct.struct_name)});
                    }
                } else {
                    structs.emplace(port_struct.struct_name, port_struct);
                    struct_ports_.emplace(port_struct.struct_name, port.get());
                }
            }
        }
    }

    std::map<std::string, PackedStruct> structs;

private:
    std::map<std::string, Port*> struct_ports_;
};

std::map<std::string, std::string> extract_struct_info(Generator* top) {
    PortPackedVisitor visitor;
    visitor.visit_generator_root(top);

    // convert the definition into
    std::map<std::string, std::string> result;
    for (auto const& [name, struct_] : visitor.structs) {
        // TODO:
        //  Use Stream class in the codegen instead to track the debugging info
        std::string entry;
        entry.append("typedef struct packed {\n");

        for (auto const& [attribute_name, width, is_signed] : struct_.attributes) {
            entry.append(::format("    logic [{0}:0] {1} {2};\n", width - 1,
                                  is_signed ? "signed" : "", attribute_name));
        }
        entry.append(::format("}} {0};\n", name));
        result.emplace(name, entry);
    }
    return result;
}

class MergeWireAssignmentsVisitor : public ASTVisitor {
public:
    void visit(Generator* generator) override {
        std::set<std::shared_ptr<Stmt>> stmts_to_remove;

        // first filter out sliced assignments
        std::set<std::shared_ptr<AssignStmt>> sliced_stmts;
        uint64_t stmt_count = generator->stmts_count();
        for (uint32_t i = 0; i < stmt_count; i++) {
            auto stmt = generator->get_stmt(i);
            if (stmt->type() == StatementType::Assign) {
                auto assign_stmt = stmt->as<AssignStmt>();
                if (assign_stmt->left()->type() == VarType::Slice &&
                    assign_stmt->right()->type() == VarType::Slice) {
                    sliced_stmts.emplace(assign_stmt);
                }
            }
        }

        // then group the assignments together
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
            if (left_parent->width != right_parent->width) continue;

            slice_vars[{left_parent, right_parent}].emplace_back(assign_stmt);
        }

        // merge the assignments
        for (auto const& [vars, stmts] : slice_vars) {
            auto& [left, right] = vars;

            // NOTE:
            // we assume that at this stage we've passed the connectivity check
            if (stmts.size() != left->width) continue;

            // remove left's sources and right's sink
            // also add it to the statements to remove
            for (auto const& stmt : stmts) {
                left->remove_source(stmt);
                right->remove_sink(stmt);
                stmts_to_remove.emplace(stmt);
            }
            // make new assignment
            auto new_stmt = left->assign(right->shared_from_this(), AssignmentType::Blocking)
                                .shared_from_this();
            generator->add_stmt(new_stmt);
            if (generator->debug) {
                // merge all the statements
                for (auto const& stmt : stmts) {
                    new_stmt->fn_name_ln.insert(new_stmt->fn_name_ln.end(),
                                                stmt->fn_name_ln.begin(), stmt->fn_name_ln.end());
                }
                new_stmt->fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
            }
        }

        for (auto const& stmt : stmts_to_remove) {
            generator->remove_stmt(stmt);
        }
    }
};

void merge_wire_assignments(Generator* top) {
    // for now we only merge generator-level assignments
    MergeWireAssignmentsVisitor visitor;
    visitor.visit_generator_root(top);
}

void PassManager::add_pass(const std::string& name, std::function<void(Generator*)> fn) {
    if (has_pass(name))
        throw ::runtime_error(::format("{0} already exists in the pass manager", name));
    passes_.emplace(name, fn);
    passes_order_.emplace_back(name);
}

void PassManager::add_pass(const std::string& name, void(fn)(Generator*)) {
    if (has_pass(name))
        throw ::runtime_error(::format("{0} already exists in the pass manager", name));
    auto func = [=](Generator* generator) { (*fn)(generator); };
    passes_.emplace(name, func);
    passes_order_.emplace_back(name);
}

void PassManager::run_passes(Generator* generator) {
    for (const auto& fn_name : passes_order_) {
        auto fn = passes_.at(fn_name);
        fn(generator);
    }
}