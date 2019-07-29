#include "pass.hh"
#include <algorithm>
#include <functional>
#include <iostream>
#include "codegen.hh"
#include "except.hh"
#include "fmt/format.h"
#include "generator.hh"
#include "port.hh"
#include "util.hh"

using fmt::format;
using std::runtime_error;

namespace kratos {

class AssignmentTypeVisitor : public IRVisitor {
public:
    explicit AssignmentTypeVisitor(AssignmentType type, bool check_type = true)
        : IRVisitor(), type_(type), check_type_(check_type) {}
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

class AssignmentTypeBlockVisitor : public IRVisitor {
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

class VerifyAssignmentVisitor : public IRVisitor {
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
            if (stmt->parent()->ir_node_kind() == IRNodeKind::GeneratorKind) {
                is_top_level = true;
                break;
            }
        }

        // second pass the check all the assignments
        bool has_error = false;
        if (is_top_level) {
            for (auto const& stmt : sources) {
                if (stmt->parent()->ir_node_kind() != IRNodeKind::GeneratorKind) {
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

class VarUnusedVisitor : public IRVisitor {
public:
    void visit(Generator* generator) override {
        std::set<std::string> vars_to_remove;
        auto vars = generator->vars();
        for (auto const& [var_name, var] : vars) {
            if (var->type() != VarType::Base) continue;
            if (var->sinks().empty() && var->sources().empty()) vars_to_remove.emplace(var_name);
        }

        // rmeove unused vars
        for (auto const& var_name : vars_to_remove) {
            generator->remove_var(var_name);
        }
    }
};

void remove_unused_vars(Generator* top) {
    VarUnusedVisitor visitor;
    visitor.visit_generator_root_p(top);
}

class UnusedTopBlockVisitor : public IRVisitor {
    void visit(Generator* generator) override {
        std::set<std::shared_ptr<Stmt>> blocks_to_remove;
        uint64_t stmt_count = generator->stmts_count();
        for (uint64_t i = 0; i < stmt_count; i++) {
            auto stmt = generator->get_stmt(i);
            if (stmt->type() == StatementType::Block) {
                auto block = dynamic_cast<StmtBlock*>(stmt.get());
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

bool connected(const std::shared_ptr<Port>& port, std::unordered_set<uint32_t>& bits) {
    bool result = false;
    bits.reserve(port->width);
    if (!port->sources().empty()) {
        // it has been assigned. need to compute all the slices
        auto sources = port->sources();
        for (auto& stmt : sources) {
            auto src = stmt->left();
            if (src->type() == VarType::Slice) {
                auto ptr = src->as<VarSlice>();
                auto low = ptr->var_low();
                auto high = ptr->var_high();
                for (uint32_t i = low; i <= high; i++) {
                    bits.emplace(i);
                }
            } else {
                result = true;
                for (uint32_t i = 0; i < port->width; i++) bits.emplace(i);
                break;
            }
        }
    }
    if (result && bits.size() != port->width) result = false;
    return result;
}

class GeneratorConnectivityVisitor : public IRVisitor {
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

            std::unordered_set<uint32_t> bits;
            bool has_error = !connected(port, bits);

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

class ZeroGeneratorInputVisitor : public IRVisitor {
public:
    void visit(Generator* generator) override {
        // we only do that with generator that has attributes called "zero_inputs"
        // we don't care about the values
        auto attributes = generator->get_attributes();
        bool has_attribute = false;
        if (!attributes.empty()) {
            for (auto const& attr : attributes) {
                if (attr->type_str == "zero_inputs") {
                    has_attribute = true;
                    break;
                }
            }
        }
        if (has_attribute) {
            // compute unconnected
            // check each child generator
            auto children = generator->get_child_generators();
            for (auto const& gen : children) {
                auto port_names = gen->get_port_names();
                for (auto const& port_name : port_names) {
                    auto port = gen->get_port(port_name);
                    if (port->port_direction() == PortDirection::Out) continue;
                    std::unordered_set<uint32_t> bits;
                    bool is_connected = connected(port, bits);
                    if (!is_connected) {
                        // notice that we can two choices here:
                        // bit wiring and bulk wiring
                        // we will implement bulk wiring here since the merge wiring pass is not
                        // complete at the time of implementation
                        // compute the set difference
                        std::vector<uint32_t> diff_bits;
                        for (uint32_t i = 0; i < port->width; i++) {
                            if (bits.find(i) == bits.end()) {
                                // no need to sort the bits since we're going in order
                                // so it's already sorted.
                                diff_bits.emplace_back(i);
                            }
                        }
                        // we will connect the size 1 easily
                        // however, if it's an array and sliced in a weird way, there is nothing
                        // easy we can do. for now we will throw an exception
                        // maximum the slices range
                        uint32_t low = diff_bits[0];
                        uint32_t high = low;
                        uint32_t pre_high = high;

                        // lambda functions to handle the situation
                        std::function<void(uint32_t, uint32_t)> wire_zero = [=](uint32_t h,
                                                                                uint32_t l) {
                            uint32_t ll, hh;
                            if (port->size == 1) {
                                ll = l;
                                hh = h;
                            } else {
                                if (l % port->var_width || (h + 1) % port->var_width) {
                                    // can't handle it right now
                                    auto stmts = std::vector<Stmt*>();
                                    stmts.reserve(port->sources().size());
                                    for (auto const& stmt : port->sources()) {
                                        stmts.emplace_back(stmt.get());
                                    }
                                    throw StmtException(
                                        "Cannot fix up unpacked array due to irregular slicing",
                                        stmts);
                                }
                                // compute the low and high
                                ll = l / port->var_width;
                                hh = h / port->var_width;
                            }
                            std::shared_ptr<AssignStmt> stmt;
                            // a special case is that the port is not connected at all!
                            if (ll == 0 && hh == (port->width - 1)) {
                                stmt = port->assign(gen->constant(0, port->width, port->is_signed));
                            } else {
                                auto& slice = port->operator[]({hh, ll});
                                stmt = slice.assign(gen->constant(0, slice.width, slice.is_signed));
                            }
                            stmt->fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
                            gen->add_stmt(stmt);
                        };

                        for (auto const bit : diff_bits) {
                            high = bit;
                            if (high - pre_high > 1) {
                                // there is a gap
                                wire_zero(pre_high, low);
                                low = high;
                                pre_high = low;
                            } else {
                                pre_high = high;
                            }
                        }
                        // the last bit
                        wire_zero(high, low);
                    }
                }
            }
        }
    }
};

void zero_generator_inputs(Generator* top) {
    ZeroGeneratorInputVisitor visitor;
    visitor.visit_generator_root_p(top);
}

class ModuleInstantiationVisitor : public IRVisitor {
public:
    void visit(Generator* generator) override {
        for (auto& child : generator->get_child_generators()) {
            // create instantiation statement
            auto stmt = std::make_shared<ModuleInstantiationStmt>(child.get(), generator);
            if (generator->debug) {
                // get the debug info from the add_generator, if possible
                auto debug_info = generator->children_debug();
                if (debug_info.find(child->instance_name) != debug_info.end()) {
                    auto info = debug_info.at(child->instance_name);
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
    visitor.visit_generator_root_p(top);
}

class UniqueGeneratorVisitor : public IRVisitor {
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
        std::unordered_map<uint64_t, Generator*> name_map;
        std::unordered_set<std::string> new_names;
        for (auto& instance : module_instances) {
            auto ptr = instance.get();
            if (context->has_hash(ptr)) {
                uint64_t hash = context->get_hash(ptr);
                if (name_map.find(hash) == name_map.end()) {
                    // need to uniquify it
                    name_map.emplace(hash, ptr);
                    if (new_names.empty()) {
                        // use the original name
                        new_names.emplace(ptr->name);
                    } else {
                        // find a new one
                        uint32_t count = new_names.size() - 1;
                        while (true) {
                            const std::string new_name = ::format("{0}_unq{1}", name, count++);
                            if (!context->generator_name_exists(new_name)) {
                                context->change_generator_name(ptr, new_name);
                                break;
                            }
                        }
                        new_names.emplace(ptr->name);
                    }
                } else {
                    // re-use the old name
                    auto old_name = name_map.at(hash)->name;
                    context->change_generator_name(ptr, old_name);
                }
            }
        }
    }
}

class GeneratorPortVisitor : public IRVisitor {
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
                            // remove it from the parent generator
                            src->generator->remove_stmt(stmt);
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
                auto& var = parent->var(new_name, port->var_width, port->size, port->is_signed);
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
                    auto src = stmt->left();
                    if (src->type() == VarType::PortIO && src->generator == generator->parent() &&
                        stmt->right() == port) {
                        // remove it from the parent generator
                        src->generator->remove_stmt(stmt);
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
                auto& var = parent->var(new_name, port->var_width, port->size, port->is_signed);
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

class StubGeneratorVisitor : public IRVisitor {
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
                generator->add_stmt(port->assign(generator->constant(0, port->width)));
            }
        }
    }
};

void zero_out_stubs(Generator* top) {
    StubGeneratorVisitor visitor;
    visitor.visit_generator_root_p(top);
}

class MixedAssignmentVisitor : public IRVisitor {
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

class TransformIfCase : public IRVisitor {
public:
    void visit(CombinationalStmtBlock* stmts) override {
        for (uint64_t i = 0; i < stmts->child_count(); i++) {
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
        if (if_->else_body()->size() > 1) return false;

        if_stmts.emplace(if_);
        if (if_->else_body()->empty()) {
            return true;
        } else if (if_->then_body()->size() > 1) {
            return if_stmts.size() > 1;
        } else {
            return has_target_if((*if_->else_body())[0].get(), var, if_stmts);
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
            if (!stmt->else_body()->empty() &&
                if_stmts.find((*stmt->else_body())[0]) == if_stmts.end()) {
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
            if (stmt->parent()->ir_node_kind() == IRNodeKind::GeneratorKind) {
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
    visitor.visit_generator_root_p(top);
}

class RemovePassThroughVisitor : public IRVisitor {
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
                    auto& new_var =
                        generator->var(var_name, port->var_width, port->size, port->is_signed);
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
    visitor.visit_generator_root_p(top);
}

// this is only for visiting the vars and assignments in the current generator
class DebugInfoVisitor : public IRVisitor {
public:
    void visit(Var* var) override { add_info(var); }

    void inline visit(AssignStmt* stmt) override { add_info(stmt); }

    void visit(Port* var) override { add_info(var); }

    void visit(SwitchStmt* stmt) override { add_info(stmt); }

    void inline visit(SequentialStmtBlock* stmt) override { add_info(stmt); }

    void inline visit(CombinationalStmtBlock* stmt) override { add_info(stmt); }

    void inline visit(ModuleInstantiationStmt* stmt) override { add_info(stmt); }

    void inline visit(IfStmt* stmt) override { add_info(stmt); }

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

class GeneratorDebugVisitor : public IRVisitor {
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

class PortPackedVisitor : public IRVisitor {
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
                    for (uint64_t i = 0; i < port_struct.attributes.size(); i++) {
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
    }

    void extract_sliced_stmts(Generator* generator,
                              std::set<std::shared_ptr<AssignStmt>>& sliced_stmts) const {
        uint64_t stmt_count = generator->stmts_count();
        for (uint64_t i = 0; i < stmt_count; i++) {
            auto stmt = generator->get_stmt(i);
            if (stmt->type() == Assign) {
                auto assign_stmt = stmt->as<AssignStmt>();
                if (assign_stmt->left()->type() == Slice && assign_stmt->right()->type() == Slice) {
                    sliced_stmts.emplace(assign_stmt);
                }
            }
        }
    }

    void extract_sliced_stmts(StmtBlock* block,
                              std::set<std::shared_ptr<AssignStmt>>& sliced_stmts) const {
        for (auto const& stmt : *block) {
            if (stmt->type() == Assign) {
                auto assign_stmt = stmt->as<AssignStmt>();
                if (assign_stmt->left()->type() == Slice && assign_stmt->right()->type() == Slice) {
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
            if (left_parent->type() == Slice) continue;
            if (right_parent->type() == Slice) continue;
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
            create_new_assignment(generator, stmts, left, right);
        }
    }
    void create_new_assignment(Generator* generator,
                               const std::vector<std::shared_ptr<AssignStmt>>& stmts,
                               Var* const left, Var* const right) const {
        auto new_stmt = left->assign(right->shared_from_this(), Blocking);
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

    void create_new_assignment(StmtBlock* block,
                               const std::vector<std::shared_ptr<AssignStmt>>& stmts,
                               Var* const left, Var* const right) const {
        auto new_stmt = left->assign(right->shared_from_this(), Blocking);
        block->add_stmt(new_stmt);
        auto generator = get_parent(block);
        if (generator->debug) {
            // merge all the statements
            for (auto const& stmt : stmts) {
                new_stmt->fn_name_ln.insert(new_stmt->fn_name_ln.end(), stmt->fn_name_ln.begin(),
                                            stmt->fn_name_ln.end());
            }
            new_stmt->fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
        }
    }

    Generator* get_parent(StmtBlock* block) const {
        Generator* result = nullptr;
        IRNode* node = block;
        for (uint32_t i = 0; i < 10000u; i++) {
            auto p = node->parent();
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
                for (auto const& port_name : port_names) {
                    auto port = generator->get_port(port_name);
                    if (port->port_type() == PortType::Clock) {
                        clock_name = port_name;
                        break;
                    }
                }
            }
            if (clock_name.empty()) {
                throw std::runtime_error(
                    ::format("Unable to find clock signal for generator {0}", generator->name));
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
                    auto& var =
                        generator->var(new_name, port->var_width, port->size, port->is_signed);
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

void PassManager::register_pass(const std::string& name, std::function<void(Generator*)> fn) {
    if (has_pass(name))
        throw ::runtime_error(::format("{0} already exists in the pass manager", name));
    passes_.emplace(name, std::move(fn));
}

void PassManager::register_pass(const std::string& name, void(fn)(Generator*)) {
    if (has_pass(name))
        throw ::runtime_error(::format("{0} already exists in the pass manager", name));
    auto func = [=](Generator* generator) { (*fn)(generator); };
    passes_.emplace(name, func);
}

void PassManager::add_pass(const std::string& name) {
    if (!has_pass(name))
        throw ::runtime_error(::format("{0} doesn't exists in the pass manager", name));
    passes_order_.emplace_back(name);
}

void PassManager::run_passes(Generator* generator) {
    for (const auto& fn_name : passes_order_) {
        auto fn = passes_.at(fn_name);
        fn(generator);
    }
}

void PassManager::register_builtin_passes() {
    register_pass("remove_pass_through_modules", &remove_pass_through_modules);

    register_pass("transform_if_to_case", &transform_if_to_case);

    register_pass("fix_assignment_type", &fix_assignment_type);

    register_pass("zero_out_stubs", &zero_out_stubs);

    register_pass("remove_fanout_one_wires", &remove_fanout_one_wires);

    register_pass("decouple_generator_ports", &decouple_generator_ports);

    register_pass("remove_unused_vars", &remove_unused_vars);

    register_pass("remove_unused_stmts", &remove_unused_stmts);

    register_pass("verify_assignments", &verify_assignments);

    register_pass("verify_generator_connectivity", &verify_generator_connectivity);

    register_pass("check_mixed_assignment", &check_mixed_assignment);

    register_pass("merge_wire_assignments", &merge_wire_assignments);

    register_pass("zero_generator_inputs", &zero_generator_inputs);

    // TODO:
    //  add inline pass

    register_pass("hash_generators_parallel", &hash_generators_parallel);
    register_pass("hash_generators_sequential", &hash_generators_sequential);

    register_pass("uniquify_generators", &uniquify_generators);

    register_pass("create_module_instantiation", &create_module_instantiation);

    register_pass("insert_pipeline_stages", &insert_pipeline_stages);

    // check the connection again, just to be safe
    add_pass("verify_generator_connectivity");
}

}