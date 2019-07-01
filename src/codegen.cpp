#include "codegen.h"
#include <fmt/format.h>
#include "NanoLog.hpp"
#include "context.hh"
#include "expr.hh"
#include "generator.hh"
#include "pass.hh"
#include "util.hh"

using fmt::format;
using std::endl;
using std::runtime_error;

void VerilogModule::run_passes(bool run_if_to_case_pass, bool remove_passthrough,
                               bool run_fanout_one_pass) {
    // run multiple passes

    if (remove_passthrough) remove_pass_through_modules(generator_);

    if (run_if_to_case_pass) transform_if_to_case(generator_);

    // LOG_INFO << "Running pass: fix_assignment_type";
    fix_assignment_type(generator_);

    zero_out_stubs(generator_);

    if (run_fanout_one_pass) remove_fanout_one_wires(generator_);

    // LOG_INFO << "Running pass:  remove_unused_vars";
    remove_unused_vars(generator_);
    verify_assignments(generator_);
    // LOG_INFO << "Running pass: verify_generator_connectivity";
    verify_generator_connectivity(generator_);
    check_mixed_assignment(generator_);
    // TODO:
    //  add decouple-wire
    //  add inline pass
    // LOG_INFO << "Running pass: uniquify_generators";
    uniquify_generators(generator_);
    // LOG_INFO << "Running pass: uniquify_module_instances";
    uniquify_module_instances(generator_);
    // LOG_INFO << "Running pass: create_module_instantiation";
    create_module_instantiation(generator_);
    // LOG_INFO << "Running pass: generate_verilog";
    verilog_src_ = generate_verilog(generator_);
}

SystemVerilogCodeGen::SystemVerilogCodeGen(Generator* generator) : generator_(generator) {
    // if it's an external file, we don't output anything
    if (generator->external()) return;

    // output module definition
    stream_ << ::format("module {0} (", generator->name) << ::endl;
    generate_ports(generator);
    stream_ << ");" << ::endl << ::endl;
    generate_variables(generator);

    for (uint32_t i = 0; i < generator->child_count(); i++) {
        dispatch_node(generator->get_child(i));
        stream_ << ::endl;
    }

    stream_ << ::format("endmodule   // {0}", generator->name) << ::endl;
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
                << ::format("{0}{1}", get_port_str(port.get()),
                            (i == port_names.size() - 1) ? "" : ",")
                << ::endl;
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
    if (skip_indent_) {
        skip_indent_ = false;
        return "";
    }
    std::string result;
    uint32_t num_indent = indent_ * indent_size;
    result.resize(num_indent);
    for (uint32_t i = 0; i < num_indent; i++) result[i] = ' ';
    return result;
}

void SystemVerilogCodeGen::dispatch_node(ASTNode* node) {
    if (node->ast_node_kind() != ASTNodeKind::StmtKind)
        throw ::runtime_error(::format("Cannot codegen non-statement node. Got {0}",
                                       ast_type_to_string(node->ast_node_kind())));
    auto stmt_ptr = reinterpret_cast<Stmt*>(node);
    if (stmt_ptr->type() == StatementType::Assign) {
        stmt_code(reinterpret_cast<AssignStmt*>(node));
    } else if (stmt_ptr->type() == StatementType::Block) {
        stmt_code(reinterpret_cast<StmtBlock*>(node));
    } else if (stmt_ptr->type() == StatementType::If) {
        stmt_code(reinterpret_cast<IfStmt*>(node));
    } else if (stmt_ptr->type() == StatementType::ModuleInstantiation) {
        stmt_code(reinterpret_cast<ModuleInstantiationStmt*>(node));
    } else if (stmt_ptr->type() == StatementType ::Switch) {
        stmt_code(reinterpret_cast<SwitchStmt*>(node));
    } else {
        throw ::runtime_error("Not implemented");
    }
}

void SystemVerilogCodeGen::stmt_code(AssignStmt* stmt) {
    // assume that it's already de-coupled the module instantiation
    if ((stmt->left()->type() == VarType::PortIO && stmt->left()->generator != generator_) ||
        (stmt->right()->type() == VarType::PortIO && stmt->right()->generator != generator_))
        return;
    const auto& left = stmt->left()->to_string();
    const auto& right = stmt->right()->to_string();
    if (stmt->parent() == generator_) {
        // top level
        if (stmt->assign_type() != AssignmentType::Blocking)
            throw ::runtime_error(
                ::format("Top level assignment for {0} <- {1} has to be blocking", left, right));
        stream_ << ::format("assign {0} = {1};", left, right) << ::endl;
    } else {
        if (stmt->assign_type() == AssignmentType::Blocking)
            stream_ << ::format("{0}{1} = {2};", indent(), left, right) << ::endl;
        else if (stmt->assign_type() == AssignmentType::NonBlocking)
            stream_ << ::format("{0}{1} <= {2};", indent(), left, right) << ::endl;
        else
            throw ::runtime_error(::format("Undefined assignment for {0} <- {1}", left, right));
    }
}

void SystemVerilogCodeGen::stmt_code(StmtBlock* stmt) {
    if (stmt->block_type() == StatementBlockType::Sequential)
        return stmt_code(reinterpret_cast<SequentialStmtBlock*>(stmt));
    else
        return stmt_code(reinterpret_cast<CombinationalStmtBlock*>(stmt));
}

void SystemVerilogCodeGen::stmt_code(SequentialStmtBlock* stmt) {
    // produce the sensitive list
    std::vector<std::string> sensitive_list;
    for (const auto& [type, var] : stmt->get_conditions()) {
        std::string edge = (type == BlockEdgeType::Posedge) ? "posedge" : "negedge";
        sensitive_list.emplace_back(::format("{0} {1}", edge, var->to_string()));
    }
    std::string sensitive_list_str = join(sensitive_list.begin(), sensitive_list.end(), ", ");
    stream_ << ::endl << "always @(" << sensitive_list_str << ") begin" << ::endl;
    indent_++;

    for (uint32_t i = 0; i < stmt->child_count(); i++) {
        dispatch_node(stmt->get_child(i));
    }

    indent_--;
    stream_ << indent() << "end" << ::endl;
}

void SystemVerilogCodeGen::stmt_code(CombinationalStmtBlock* stmt) {
    stream_ << "always_comb begin" << ::endl;
    indent_++;

    for (uint32_t i = 0; i < stmt->child_count(); i++) {
        dispatch_node(stmt->get_child(i));
    }

    indent_--;
    stream_ << indent() << "end" << ::endl << ::endl;
}

void SystemVerilogCodeGen::stmt_code(IfStmt* stmt) {
    stream_ << indent() << ::format("if ({0}) begin", stmt->predicate()->to_string()) << ::endl;
    indent_++;

    auto const& then_body = stmt->then_body();
    for (auto const& child : then_body) {
        dispatch_node(child.get());
    }

    indent_--;
    stream_ << indent() << "end" << ::endl;

    auto const& else_body = stmt->else_body();
    if (!else_body.empty()) {
        // special case where there is another (and only) if statement nested inside the else body
        // i.e. the else if case
        bool skip = false;
        if (else_body.size() == 1) {
            auto const if_stmt = else_body[0];
            if (if_stmt->type() == StatementType::If) {
                skip = true;
            }
        }
        if (skip) {
            stream_ << indent() << "else ";
            skip_indent_ = true;
            dispatch_node(else_body[0].get());
        } else {
            stream_ << indent() << "else begin" << ::endl;
            indent_++;

            for (auto const& child : else_body) {
                dispatch_node(child.get());
            }
            indent_--;

            stream_ << indent() << "end" << ::endl;
        }
    }
}

void SystemVerilogCodeGen::stmt_code(ModuleInstantiationStmt* stmt) {
    stream_ << indent() << stmt->target()->name << " " << stmt->target()->instance_name << " ("
            << std::endl;
    indent_++;
    uint32_t count = 0;
    for (auto const& [internal, external] : stmt->port_mapping()) {
        const auto& end = count++ < stmt->port_mapping().size() - 1 ? ")," : ")";
        stream_ << indent() << "." << internal->to_string() << "(" << external->to_string() << end
                << std::endl;
    }
    stream_ << ");" << std::endl << std::endl;
    indent_--;
}

void SystemVerilogCodeGen::stmt_code(SwitchStmt* stmt) {
    stream_ << indent() << "case (" << stmt->target()->to_string() << ")" << ::endl;
    indent_++;
    auto const& body = stmt->body();
    for (auto& iter : body) {
        stream_ << indent() << (iter.first ? iter.first->to_string() : "default") << ": ";
        if (iter.second.empty()) {
            throw ::runtime_error(
                ::format("Switch statement condition {0} is empty!", iter.first->to_string()));
        } else {
            stream_ << "begin" << ::endl;
            indent_++;

            for (auto const& st : iter.second) dispatch_node(st.get());

            indent_--;
            stream_ << indent() << "end" << ::endl;
        }
    }

    indent_--;
    stream_ << indent() << "endcase" << ::endl;
}

bool is_port_reg(Port* port) {
    if (port->port_direction() != PortDirection::Out) return false;
    bool is_reg = false;
    for (auto const& stmt : port->sources()) {
        if (!stmt->parent())  // top level assignments
            return false;
        if (stmt->parent()->ast_node_kind() != ASTNodeKind::GeneratorKind) {
            is_reg = true;
            break;
        }
    }
    // slices
    if (!is_reg) {
        for (auto const& iter : port->get_slices()) {
            if (is_reg) break;
            auto slice = iter.second;
            for (auto const& stmt : slice->sources()) {
                if (stmt->parent()->ast_node_kind() != ASTNodeKind::GeneratorKind) {
                    is_reg = true;
                    break;
                }
            }
        }
    }
    return is_reg;
}

std::string SystemVerilogCodeGen::get_port_str(Port* port) {
    std::vector<std::string> strs;
    strs.reserve(8);
    strs.emplace_back(port_dir_to_str(port->port_direction()));
    if (port->is_signed) strs.emplace_back("signed");
    if (is_port_reg(port)) {
        strs.emplace_back("reg");
    }
    strs.emplace_back(get_var_width_str(port));
    strs.emplace_back(port->name);

    return join(strs.begin(), strs.end(), " ");
}