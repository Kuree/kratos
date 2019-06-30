#include "codegen.h"
#include <fmt/format.h>
#include "NanoLog.hpp"
#include "context.hh"
#include "expr.hh"
#include "generator.hh"
#include "pass.hh"
#include "util.hh"

using fmt::format;
using std::runtime_error;

VerilogModule::VerilogModule(Generator* generator) {
    // run multiple passes
    // LOG_INFO << "Running pass: fix_assignment_type";
    fix_assignment_type(generator);

    zero_out_stubs(generator);

    // LOG_INFO << "Running pass:  remove_unused_vars";
    remove_unused_vars(generator);
    verify_assignments(generator);
    // LOG_INFO << "Running pass: verify_generator_connectivity";
    verify_generator_connectivity(generator);
    check_mixed_assignment(generator);
    // TODO:
    //  add decouple-wire
    //  add inline pass
    // LOG_INFO << "Running pass: create_module_instantiation";
    create_module_instantiation(generator);
    // LOG_INFO << "Running pass: uniquify_generators";
    uniquify_generators(generator);
    // LOG_INFO << "Running pass: uniquify_module_instances";
    uniquify_module_instances(generator);
    // LOG_INFO << "Running pass: create_module_instantiation";
    create_module_instantiation(generator);
    // LOG_INFO << "Running pass: generate_verilog";
    verilog_src_ = generate_verilog(generator);
}

SystemVerilogCodeGen::SystemVerilogCodeGen(Generator* generator) : generator_(generator) {
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

std::string SystemVerilogCodeGen::get_var_width_str(const Var* var) {
    return var->width > 1 ? ::format("[{0}:0]", var->width - 1) : "";
}

void SystemVerilogCodeGen::generate_ports(Generator* generator) {
    indent_++;
    // sort the names
    auto& port_names_set = generator->get_port_names();
    std::vector<std::string> port_names(port_names_set.begin(), port_names_set.end());
    std::sort(port_names.begin(), port_names.end());
    for (uint32_t i = 0; i < port_names.size(); i++) {
        auto const& port_name = port_names[i];
        auto port = generator->get_port(port_name);
        stream_ << indent()
                << ::format("{0}{1}\n", get_port_str(port.get()),
                            (i == port_names.size() - 1) ? "" : ",");
    }
    indent_--;
}

void SystemVerilogCodeGen::generate_variables(Generator* generator) {
    auto const& vars = generator->get_vars();
    for (auto const& var_name : vars) {
        auto const& var = generator->get_var(var_name);
        if (var->type() == VarType::Base) {
            stream_ << ::format("logic {0} {1} {2};", var->is_signed ? "signed" : "",
                                get_var_width_str(var.get()), var->name)
                    << std::endl;
        }
    }
}

std::string SystemVerilogCodeGen::indent() {
    std::string result;
    uint32_t num_indent = indent_ * indent_size;
    result.resize(num_indent);
    for (uint32_t i = 0; i < num_indent; i++) result[i] = ' ';
    return result;
}

std::string SystemVerilogCodeGen::dispatch_str(ASTNode* node) {
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

std::string SystemVerilogCodeGen::to_string(AssignStmt* stmt) {
    // assume that it's already de-coupled the module instantiation
    if ((stmt->left()->type() == VarType::PortIO && stmt->left()->generator != generator_) ||
        (stmt->right()->type() == VarType::PortIO && stmt->right()->generator != generator_))
        return "";
    const auto& left = stmt->left()->to_string();
    const auto& right = stmt->right()->to_string();
    if (stmt->parent() == generator_) {
        // top level
        if (stmt->assign_type() != AssignmentType::Blocking)
            throw ::runtime_error(
                ::format("Top level assignment for {0} <- {1} has to be blocking", left, right));
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

std::string SystemVerilogCodeGen::to_string(StmtBlock* stmt) {
    if (stmt->block_type() == StatementBlockType::Sequential)
        return to_string(reinterpret_cast<SequentialStmtBlock*>(stmt));
    else
        return to_string(reinterpret_cast<CombinationalStmtBlock*>(stmt));
}

std::string SystemVerilogCodeGen::to_string(SequentialStmtBlock* stmt) {
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

std::string SystemVerilogCodeGen::to_string(CombinationalStmtBlock* stmt) {
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

std::string SystemVerilogCodeGen::to_string(IfStmt* stmt) {
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

std::string SystemVerilogCodeGen::to_string(ModuleInstantiationStmt* stmt) {
    std::stringstream sstream;
    sstream << indent() << stmt->target()->name << " " << stmt->target()->instance_name << " ("
            << std::endl;
    indent_++;
    uint32_t count = 0;
    for (auto const& [internal, external] : stmt->port_mapping()) {
        const auto& end = count++ < stmt->port_mapping().size() - 1 ? ")," : ")";
        sstream << indent() << "." << internal->to_string() << "(" << external->to_string() << end
                << std::endl;
    }
    sstream << ");" << std::endl << std::endl;
    indent_--;
    return sstream.str();
}

std::string SystemVerilogCodeGen::get_port_str(Port* port) {
    std::vector<std::string> strs;
    strs.reserve(8);
    strs.emplace_back(port_dir_to_str(port->port_direction()));
    if (port->is_signed) strs.emplace_back("signed");
    if (port->port_direction() == PortDirection::Out &&
        (*port->sources().begin())->assign_type() == AssignmentType::NonBlocking) {
        strs.emplace_back("reg");
    }
    strs.emplace_back(get_var_width_str(port));
    strs.emplace_back(port->name);

    return join(strs.begin(), strs.end(), " ");
}