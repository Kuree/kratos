#include "pass.hh"
#include <algorithm>
#include <sstream>
#include "fmt/format.h"
#include "generator.hh"

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
            throw ::runtime_error(::format("mismatch in assignment type"));
        }
    }

private:
    AssignmentType type_;
    bool check_type_;
};

class AssignmentTypeBlockVisitor : public ASTVisitor {
    void visit(CombinationalStmtBlock* block) override {
        AssignmentTypeVisitor visitor(AssignmentType::NonBlocking, true);
        visitor.visit_root(block->ast_node());
    }
    void visit(SequentialStmtBlock* block) override {
        AssignmentTypeVisitor visitor(AssignmentType::NonBlocking, true);
        visitor.visit_root(block->ast_node());
    }
};

void fix_assignment_type(Generator* generator) {
    // first we fix all the block assignment
    AssignmentTypeBlockVisitor visitor;
    visitor.visit_root(generator->ast_node());

    // then we assign any existing assignment as blocking assignment
    AssignmentTypeVisitor final_visitor(AssignmentType::Blocking, false);
    final_visitor.visit_root(generator->ast_node());
}

class VarAccumulationVisitor : public ASTVisitor {
public:
    VarAccumulationVisitor() : ASTVisitor(), vars() {}
    void visit(Var* var) override {
        if (var->type() == VarType ::Base) vars.emplace(var->name);
    }
    std::set<std::string> vars;
};

void remove_unused_vars(Generator* generator) {
    // get a set of all variables
    std::set<std::string> var_names;
    for (auto const& [var_name, var] : generator->vars()) {
        if (var->type() == VarType::Base) var_names.emplace(var_name);
    }
    // visit each assignment to see if we have used it or not
    VarAccumulationVisitor visitor;
    visitor.visit_root(generator);

    // result set
    std::set<std::string> diff_set;
    std::set_difference(var_names.begin(), var_names.end(), visitor.vars.begin(),
                        visitor.vars.end(), std::inserter(diff_set, diff_set.end()));
    for (const auto& var_name : diff_set) {
        generator->remove_var(var_name);
    }
}

class GeneratorConnectivityVisitor : public ASTVisitor {
public:
    GeneratorConnectivityVisitor() : is_top_level_(true) {}
    void visit_generator(Generator* generator) override {
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

void verify_generator_connectivity(Generator* generator) {
    GeneratorConnectivityVisitor visitor;
    visitor.visit_generator_root(generator);
}

class ModuleInstantiationVisitor : public ASTVisitor {
public:
    void visit(Generator* generator) override {
        for (auto& child : generator->get_child_generators()) {
            if (!generator->should_child_inline(child.get())) {
                // create instantiation statement
                auto stmt = ModuleInstantiationStmt(child.get(), generator);
                generator->add_stmt(stmt.shared_from_this());
            }
        }
    }
};

void create_module_instantiation(Generator* generator) {
    ModuleInstantiationVisitor visitor;
    visitor.visit_generator_root(generator);
}

class UniqueGeneratorVisitor : public ASTVisitor {
public:
    std::map<std::string, Generator*> generator_map;

    void visit_generator_root(Generator* generator) override {
        visit(generator);
        ASTVisitor::visit_generator_root(generator);
    }

    void visit(Generator* generator) override {
        if (generator_map.find(generator->name) != generator_map.end()) return;
        // a unique one
        if (!generator->external()) generator_map.emplace(generator->name, generator);
    }
};

class SystemVerilogCodeGen {
public:
    explicit SystemVerilogCodeGen(Generator* generator) : generator_(generator) {
        // output module definition
        stream_ << ::format("module {0} (\n", generator->name);
        generate_ports(generator);
        stream_ << ");\n";

        for (uint32_t i = 0; i < generator->child_count(); i++) {
            stream_ << dispatch_str(generator->get_child(i));
        }

        stream_ << ::format("\nendmodule   // {0}\n", generator->name);
    }
    const std::string str() { return stream_.str(); }

private:
    uint32_t indent_ = 0;
    std::stringstream stream_;
    Generator* generator_;

    void generate_ports(Generator* generator) {
        // sort the names
        auto& port_names_set = generator->get_port_names();
        std::vector<std::string> port_names(port_names_set.begin(), port_names_set.end());
        std::sort(port_names.begin(), port_names.end());
        for (uint32_t i = 0; i < port_names.size(); i++) {
            auto const& port_name = port_names[i];
            auto port = generator->get_port(port_name);
            stream_ << indent()
                    << ::format("{0} {1} {2} {3}{4}\n", get_port_dir_name(port->port_direction()),
                                port->is_signed ? "signed" : "",
                                port->width > 1 ? ::format("[{0}:0]", port->width - 1) : "",
                                port_name, (i == port_names.size() - 1) ? "" : ",");
        }
    }

    static std::string get_port_dir_name(PortDirection direction) {
        if (direction == PortDirection::In) {
            return "input";
        } else if (direction == PortDirection::Out) {
            return "output";
        } else {
            return "inout";
        }
    }

    std::string indent() {
        std::string result;
        result.resize(indent_);
        for (uint32_t i = 0; i < indent_; i++) result[i] = ' ';
        return result;
    }

    std::string dispatch_str(ASTNode* node) {
        if (node->ast_node_type() != ASTNodeKind::StmtKind)
            throw ::runtime_error("Cannot codegen non-statement node");
        auto stmt_ptr = reinterpret_cast<Stmt*>(node);
        if (stmt_ptr->type() == StatementType::Assign) {
            return to_string(reinterpret_cast<AssignStmt*>(node));
        } else if (stmt_ptr->type() == StatementType::Block) {
            return to_string(reinterpret_cast<StmtBlock*>(node));
        } else if (stmt_ptr->type() == StatementType::If) {
            return to_string(reinterpret_cast<IfStmt*>(node));
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
        sstream << "\nalways @(" << sensitive_list_str << ") begin";
        indent_++;

        for (uint32_t i = 0; i < stmt->child_count(); i++) {
            sstream << dispatch_str(stmt->get_child(i));
        }

        indent_--;
        sstream << "end\n";
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
        sstream << "end\n\n";
        return sstream.str();
    }

    std::string to_string(IfStmt* stmt) {
        std::stringstream sstream;
        sstream << ::format("if ({0}) begin\n", stmt->predicate()->to_string());
        indent_++;

        for (uint32_t i = 0; i < stmt->child_count(); i++) {
            sstream << dispatch_str(stmt->get_child(i));
        }

        indent_--;
        sstream << "end\n";
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

std::map<std::string, std::string> generate_verilog(Generator* generator) {
    // this pass assumes that all the generators has been uniquified
    std::map<std::string, std::string> result;
    // first get all the unique generators
    UniqueGeneratorVisitor unique_visitor;
    unique_visitor.visit_generator_root(generator);
    for (auto& [module_name, module_gen] : unique_visitor.generator_map) {
        SystemVerilogCodeGen codegen(module_gen);
        result.emplace(module_name, codegen.str());
    }
    return result;
}