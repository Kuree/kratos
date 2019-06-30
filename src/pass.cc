#include "pass.hh"
#include <algorithm>
#include <iostream>
#include <sstream>
#include "fmt/format.h"
#include "generator.hh"
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
    visitor.visit_root(top->ast_node());

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
            throw ::runtime_error(
                ::format("assignment width doesn't match. left ({0}): {1} right ({2}): {3}",
                         left->to_string(), left->width, right->to_string(), right->width));
        if (left->is_signed != right->is_signed)
            throw ::runtime_error(
                ::format("assignment sign doesn't match. left ({0}): {1} right ({2}): {3}",
                         left->to_string(), left->is_signed, right->to_string(), right->is_signed));
    }

private:
    Generator* generator_;
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
    void visit_generator(Generator* generator) override {
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

            if (!port->sources().empty()) {
                // it has been assigned
                continue;
            }
            // check the slices
            std::unordered_set<uint32_t> bits;
            auto slices = port->get_slices();
            for (auto const& [slice, slice_ptr] : slices) {
                if (!slice_ptr->sources().empty()) {
                    // we have a connection
                    // fill in the bits
                    auto [low, high] = slice;
                    for (uint32_t i = low; i <= high; i++) {
                        bits.emplace(i);
                    }
                }
            }
            for (uint32_t i = 0; i < port->width; i++) {
                if (bits.find(i) == bits.end())
                    throw ::runtime_error(::format(
                        "{0}[{1}] is a floating net. Please check your connections", port_name, i));
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
    void visit_generator(Generator* generator) override {
        for (auto& child : generator->get_child_generators()) {
            if (!generator->should_child_inline(child.get())) {
                // create instantiation statement
                auto stmt = std::make_shared<ModuleInstantiationStmt>(child.get(), generator);
                generator->add_stmt(stmt);
            }
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

    void visit_generator(Generator* generator) override { visit(generator); }

    void visit(Generator* generator) override {
        if (generator_map.find(generator->name) != generator_map.end()) return;
        // a unique one
        if (!generator->external()) generator_map.emplace(generator->name, generator);
    }
};

class SystemVerilogCodeGen {
public:
    explicit SystemVerilogCodeGen(Generator* generator) : generator_(generator) {
        // if it's an external file, we don't output anything
        if (generator->external()) return;

        // output module definition
        stream_ << ::format("module {0} (\n", generator->name);
        generate_ports(generator);
        stream_ << ");\n\n";
        generate_variables(generator);

        for (uint32_t i = 0; i < generator->child_count(); i++) {
            stream_ << dispatch_str(generator->get_child(i));
        }

        stream_ << ::format("\nendmodule   // {0}\n", generator->name);
    }
    const std::string str() { return stream_.str(); }

    uint32_t indent_size = 2;

private:
    uint32_t indent_ = 0;
    std::stringstream stream_;
    Generator* generator_;

    static inline std::string get_var_width_str(const std::shared_ptr<Var>& var) {
        return var->width > 1 ? ::format("[{0}:0]", var->width - 1) : "";
    }

    void generate_ports(Generator* generator) {
        indent_++;
        // sort the names
        auto& port_names_set = generator->get_port_names();
        std::vector<std::string> port_names(port_names_set.begin(), port_names_set.end());
        std::sort(port_names.begin(), port_names.end());
        for (uint32_t i = 0; i < port_names.size(); i++) {
            auto const& port_name = port_names[i];
            auto port = generator->get_port(port_name);
            stream_ << indent()
                    << ::format("{0} {1} {2} {3}{4}\n", port_dir_to_str(port->port_direction()),
                                port->is_signed ? "signed" : "", get_var_width_str(port), port_name,
                                (i == port_names.size() - 1) ? "" : ",");
        }
        indent_--;
    }

    void generate_variables(Generator* generator) {
        auto const& vars = generator->get_vars();
        for (auto const& var_name : vars) {
            auto const& var = generator->get_var(var_name);
            if (var->type() == VarType::Base) {
                stream_ << ::format("logic {0} {1} {2};", var->is_signed ? "signed" : "",
                                    get_var_width_str(var), var->name)
                        << std::endl;
            }
        }
    }

    std::string indent() {
        std::string result;
        uint32_t num_indent = indent_ * indent_size;
        result.resize(num_indent);
        for (uint32_t i = 0; i < num_indent; i++) result[i] = ' ';
        return result;
    }

    std::string dispatch_str(ASTNode* node) {
        if (node->ast_node_type() != ASTNodeKind::StmtKind)
            throw ::runtime_error(::format("Cannot codegen non-statement node. Got {0}",
                                           ast_type_to_string(node->ast_node_type())));
        auto stmt_ptr = reinterpret_cast<Stmt*>(node);
        if (stmt_ptr->type() == StatementType::Assign) {
            return to_string(reinterpret_cast<AssignStmt*>(node));
        } else if (stmt_ptr->type() == StatementType::Block) {
            return to_string(reinterpret_cast<StmtBlock*>(node));
        } else if (stmt_ptr->type() == StatementType::If) {
            return to_string(reinterpret_cast<IfStmt*>(node));
        } else if (stmt_ptr->type() == StatementType::ModuleInstantiation) {
            return to_string(reinterpret_cast<ModuleInstantiationStmt*>(node));
        } else {
            throw ::runtime_error("Not implemented");
        }
    }

    std::string to_string(AssignStmt* stmt) {
        // assume that it's already de-coupled the module instantiation
        if ((stmt->left()->type() == VarType::PortIO && stmt->left()->generator != generator_) ||
            (stmt->right()->type() == VarType::PortIO && stmt->right()->generator != generator_))
            return "";
        const auto& left = stmt->left()->to_string();
        const auto& right = stmt->right()->to_string();
        if (stmt->parent() == generator_) {
            // top level
            if (stmt->assign_type() != AssignmentType::Blocking)
                throw ::runtime_error(::format(
                    "Top level assignment for {0} <- {1} has to be blocking", left, right));
            return ::format("assign {0} = {1};\n", left, right);
        } else {
            if (stmt->assign_type() == AssignmentType::Blocking)
                return ::format("{0}{1} = {2};\n", indent(), left, right);
            else if (stmt->assign_type() == AssignmentType::NonBlocking)
                return ::format("{0}{1} <= {2};\n", indent(), left, right);
            else
                throw ::runtime_error(::format("Undefined assignment for {0} <- {1}", left, right));
        }
    }

    std::string to_string(StmtBlock* stmt) {
        if (stmt->block_type() == StatementBlockType::Sequential)
            return to_string(reinterpret_cast<SequentialStmtBlock*>(stmt));
        else
            return to_string(reinterpret_cast<CombinationalStmtBlock*>(stmt));
    }

    std::string to_string(SequentialStmtBlock* stmt) {
        // produce the sensitive list
        std::vector<std::string> sensitive_list;
        for (const auto& [type, var] : stmt->get_conditions()) {
            std::string edge = (type == BlockEdgeType::Posedge) ? "posedge" : "negedge";
            sensitive_list.emplace_back(::format("{0} {1}", edge, var->to_string()));
        }
        std::stringstream sstream;
        std::string sensitive_list_str = join(sensitive_list.begin(), sensitive_list.end(), ", ");
        sstream << "\nalways @(" << sensitive_list_str << ") begin\n";
        indent_++;

        for (uint32_t i = 0; i < stmt->child_count(); i++) {
            sstream << dispatch_str(stmt->get_child(i));
        }

        indent_--;
        sstream << indent() << "end\n";
        return sstream.str();
    }

    std::string to_string(CombinationalStmtBlock* stmt) {
        std::stringstream sstream;
        sstream << "\nalways_comb begin\n";
        indent_++;

        for (uint32_t i = 0; i < stmt->child_count(); i++) {
            sstream << dispatch_str(stmt->get_child(i));
        }

        indent_--;
        sstream << indent() << "end\n\n";
        return sstream.str();
    }

    std::string to_string(IfStmt* stmt) {
        std::string s(indent());
        s.append(::format("if ({0}) begin\n", stmt->predicate()->to_string()));
        indent_++;

        auto const& then_body = stmt->then_body();
        for (auto const& child : then_body) {
            s.append(dispatch_str(child.get()));
        }

        indent_--;
        s.append(indent()).append("end\n");

        auto const& else_body = stmt->else_body();
        if (!else_body.empty()) {
            s.append(indent()).append("else begin\n");
            indent_++;

            for (auto const& child : else_body) {
                s.append(dispatch_str(child.get()));
            }
            indent_--;
        }
        s.append(indent()).append("end\n");
        return s;
    }

    std::string to_string(ModuleInstantiationStmt* stmt) {
        std::stringstream sstream;
        sstream << indent() << stmt->target()->name << " " << stmt->target()->instance_name << " ("
                << std::endl;
        indent_++;
        uint32_t count = 0;
        for (auto const& [internal, external] : stmt->port_mapping()) {
            const auto& end = count++ < stmt->port_mapping().size() - 1 ? ")," : ")";
            sstream << indent() << "." << internal->to_string() << "(" << external->to_string()
                    << end << std::endl;
        }
        sstream << ");" << std::endl << std::endl;
        indent_--;
        return sstream.str();
    }

    template <typename Iter>
    std::string join(Iter begin, Iter end, const std::string& sep) {
        std::stringstream stream;
        for (auto it = begin; it != end; it++) {
            if (it != begin) stream << sep;
            stream << *it;
        }
        return stream.str();
    }
};

std::map<std::string, std::string> generate_verilog(Generator* top) {
    // this pass assumes that all the generators has been uniquified
    std::map<std::string, std::string> result;
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
    void visit_generator(Generator* generator) override {
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
    void visit_generator(Generator* generator) override {
        if (!generator->parent()) {
            // this is top level module, no need to worry about it
            return;
        }
        auto const& port_names = generator->get_port_names();

        for (auto const& port_name : port_names) {
            auto port = generator->get_port(port_name);
            auto const port_direction = port->port_direction();
            if (port_direction == PortDirection::In) {
                // if we're connected to a base variable and no slice, we are good
                const auto slices = port->get_slices();
                const auto& sources = port->sources();
                // because an input cannot be an register, it can only has one
                // source (all bits combined)
                if (slices.empty()) {
                    if (sources.empty())
                        throw ::runtime_error(
                            ::format("{0}.{1} is not connected", generator->name, port_name));
                    if (sources.size() > 1)
                        throw ::runtime_error(::format("{0}.{1} is driven by multiple nets",
                                                       generator->name, port_name));
                    // add it to the port mapping and we are good to go
                    auto const& stmt = *sources.begin();
                    // if the source is not a base variable, create one and use it to connect
                    // otherwise we're good to go.
                    auto src = stmt->right();
                    if (src->type() == VarType::Base ||
                        (src->type() == VarType::PortIO && src->parent() == generator->parent())) {
                        continue;
                    }
                } else {
                    // we can't have a port that is driven by slice and variables
                    if (!sources.empty())
                        throw ::runtime_error(
                            ::format("{0}.{1} is over-connected", generator->name, port_name));
                }
                // create a new variable
                auto ast_parent = generator->parent();
                if (!ast_parent)
                    throw ::runtime_error(::format(
                        "{0}'s parent is empty but it's not a top module", generator->name));
                auto parent = reinterpret_cast<Generator*>(ast_parent);
                auto new_name = parent->get_unique_variable_name(generator->name, port_name);
                auto& var = parent->var(new_name, port->width, port->is_signed);
                // replace all the sources
                Var::move_src_to(port.get(), &var, parent);
            } else if (port_direction == PortDirection::Out) {
                // same logic as the port dir in
                // if we're connected to a base variable and no slice, we are good
                const auto slices = port->get_slices();
                const auto& sinks = port->sinks();
                if (slices.empty()) {
                    if (sinks.size() <= 1) {
                        // we're good to go since we can re-use the sink variables, or don't even
                        // bother to connect since no one is using it
                        continue;
                    }
                }
                // create a new variable
                auto ast_parent = generator->parent();
                if (!ast_parent)
                    throw ::runtime_error(::format(
                        "{0}'s parent is empty but it's not a top module", generator->name));
                auto parent = reinterpret_cast<Generator*>(ast_parent);
                auto new_name = parent->get_unique_variable_name(generator->name, port_name);
                auto& var = parent->var(new_name, port->width, port->is_signed);
                // replace all the sources
                Var::move_sink_to(port.get(), &var, parent);
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
    void visit_generator(Generator* generator) override {
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