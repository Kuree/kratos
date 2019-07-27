#include "codegen.hh"
#include <fmt/format.h>
#include "context.hh"
#include "except.hh"
#include "expr.hh"
#include "generator.hh"
#include "pass.hh"
#include "util.hh"

using fmt::format;
using std::runtime_error;

namespace kratos {

Stream::Stream(Generator* generator, SystemVerilogCodeGen* codegen)
    : generator_(generator), codegen_(codegen), line_no_(1) {}

Stream& Stream::operator<<(AssignStmt* stmt) {
    const auto& left = stmt->left()->to_string();
    const auto& right = stmt->right()->to_string();
    if (generator_->debug) {
        stmt->verilog_ln = line_no_;
    }

    if (stmt->parent() == generator_) {
        // top level
        if (stmt->assign_type() != AssignmentType::Blocking)
            throw ::runtime_error(
                ::format("Top level assignment for {0} <- {1} has to be blocking", left, right));
        (*this) << ::format("assign {0} = {1};", left, right) << endl();
    } else {
        if (stmt->assign_type() == AssignmentType::Blocking)
            (*this) << ::format("{0}{1} = {2};", codegen_->indent(), left, right) << endl();
        else if (stmt->assign_type() == AssignmentType::NonBlocking)
            (*this) << ::format("{0}{1} <= {2};", codegen_->indent(), left, right) << endl();
        else
            throw ::runtime_error(::format("Undefined assignment for {0} <- {1}", left, right));
    }
    return *this;
}

Stream& Stream::operator<<(const std::pair<Port*, std::string>& port) {
    auto& [p, end] = port;
    if (generator_->debug) {
        p->verilog_ln = line_no_;
    }

    (*this) << codegen_->indent() << SystemVerilogCodeGen::get_port_str(p) << end << endl();

    return *this;
}

Stream& Stream::operator<<(const std::shared_ptr<Var>& var) {
    if (generator_->debug) {
        var->verilog_ln = line_no_;
    }

    (*this) << ::format("logic {0} {1} {2}{3};", var->is_signed ? "signed" : "",
                        SystemVerilogCodeGen::get_var_width_str(var.get()), var->name,
                        var->size == 1 ? "" : ::format("[{0}:0]", var->size - 1))
            << endl();
    return *this;
}

void VerilogModule::run_passes() {
    // run multiple passes using pass manager
    // run the passes
    manager_.run_passes(generator_);
}

std::map<std::string, std::string> VerilogModule::verilog_src() {
    return generate_verilog(generator_);
}

SystemVerilogCodeGen::SystemVerilogCodeGen(Generator* generator)
    : stream_(generator, this), generator_(generator) {
    // if it's an external file, we don't output anything
    if (generator->external()) return;

    // output module definition
    stream_ << ::format("module {0} (", generator->name) << stream_.endl();
    generate_ports(generator);
    stream_ << ");" << stream_.endl() << stream_.endl();
    generate_parameters(generator);
    generate_variables(generator);

    for (uint64_t i = 0; i < generator->stmts_count(); i++) {
        dispatch_node(generator->get_stmt(i).get());
    }

    stream_ << ::format("endmodule   // {0}", generator->name) << stream_.endl();
}

std::string SystemVerilogCodeGen::get_var_width_str(const Var* var) {
    return var->var_width > 1 ? ::format("[{0}:0]", var->var_width - 1) : "";
}

void SystemVerilogCodeGen::generate_ports(Generator* generator) {
    indent_++;
    // sort the names
    auto& port_names_set = generator->get_port_names();
    std::vector<std::string> port_names(port_names_set.begin(), port_names_set.end());
    std::sort(port_names.begin(), port_names.end());
    for (uint64_t i = 0; i < port_names.size(); i++) {
        auto const& port_name = port_names[i];
        auto port = generator->get_port(port_name);
        stream_ << std::make_pair(port.get(), (i == port_names.size() - 1) ? "" : ",");
    }
    indent_--;
}

void SystemVerilogCodeGen::generate_variables(Generator* generator) {
    auto const& vars = generator->get_vars();
    for (auto const& var_name : vars) {
        auto const& var = generator->get_var(var_name);
        if (var->type() == VarType::Base) {
            stream_ << var;
        }
    }
}

void SystemVerilogCodeGen::generate_parameters(Generator* generator) {
    auto& params = generator->get_params();
    for (auto const& [name, param] : params) {
        stream_ << ::format("parameter {0} = {1};", name, param->value_str()) << stream_.endl();
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

void SystemVerilogCodeGen::dispatch_node(IRNode* node) {
    if (node->ir_node_kind() != IRNodeKind::StmtKind)
        throw ::runtime_error(::format("Cannot codegen non-statement node. Got {0}",
                                       ast_type_to_string(node->ir_node_kind())));
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
    if (stmt->left()->type() == VarType::PortIO) {
        auto port = stmt->left()->as<Port>();
        if (port->port_direction() == PortDirection::In && stmt->left()->generator == generator_) {
            throw StmtException("Cannot drive a module's input from itself", {stmt});
        }
    }
    stream_ << stmt;
}

void SystemVerilogCodeGen::stmt_code(StmtBlock* stmt) {
    switch (stmt->block_type()) {
        case StatementBlockType::Sequential: {
            stmt_code(reinterpret_cast<SequentialStmtBlock*>(stmt));
            break;
        }
        case StatementBlockType::Combinational: {
            stmt_code(reinterpret_cast<CombinationalStmtBlock*>(stmt));
            break;
        }
        case StatementBlockType::Scope: {
            stmt_code(reinterpret_cast<ScopedStmtBlock*>(stmt));
            break;
        }
    }
}

void SystemVerilogCodeGen::stmt_code(SequentialStmtBlock* stmt) {
    // produce the sensitive list
    if (generator_->debug) {
        stmt->verilog_ln = stream_.line_no();
    }
    std::vector<std::string> sensitive_list;
    for (const auto& [type, var] : stmt->get_conditions()) {
        std::string edge = (type == BlockEdgeType::Posedge) ? "posedge" : "negedge";
        sensitive_list.emplace_back(::format("{0} {1}", edge, var->to_string()));
    }
    std::string sensitive_list_str = join(sensitive_list.begin(), sensitive_list.end(), ", ");
    stream_ << stream_.endl() << "always @(" << sensitive_list_str << ") begin" << stream_.endl();
    indent_++;

    for (uint64_t i = 0; i < stmt->child_count(); i++) {
        dispatch_node(stmt->get_child(i));
    }

    indent_--;
    stream_ << indent() << "end" << stream_.endl();
}

void SystemVerilogCodeGen::stmt_code(CombinationalStmtBlock* stmt) {
    if (generator_->debug) {
        stmt->verilog_ln = stream_.line_no();
    }
    stream_ << "always_comb begin" << stream_.endl();
    indent_++;

    for (uint64_t i = 0; i < stmt->child_count(); i++) {
        dispatch_node(stmt->get_child(i));
    }

    indent_--;
    stream_ << indent() << "end" << stream_.endl();
}

void SystemVerilogCodeGen::stmt_code(kratos::ScopedStmtBlock* stmt) {
    if (generator_->debug) {
        stmt->verilog_ln = stream_.line_no();
    }

    stream_ << "begin" << stream_.endl();
    indent_++;

    for (uint64_t i = 0; i < stmt->child_count(); i++) {
        dispatch_node(stmt->get_child(i));
    }

    indent_--;
    stream_ << indent() << "end" << stream_.endl();
}

void SystemVerilogCodeGen::stmt_code(IfStmt* stmt) {
    if (generator_->debug) {
        stmt->verilog_ln = stream_.line_no();
        stmt->predicate()->verilog_ln = stream_.line_no();
    }
    stream_ << indent() << ::format("if ({0}) ", stmt->predicate()->to_string());
    auto const& then_body = stmt->then_body();
    dispatch_node(then_body.get());

    auto const& else_body = stmt->else_body();
    if (!else_body->empty()) {
        // special case where there is another (and only) if statement nested inside the else body
        // i.e. the else if case
        bool skip = else_body->size() == 1;
        if (skip) {
            stream_ << indent() << "else ";
            skip_indent_ = true;
            dispatch_node((*else_body)[0].get());
        } else {
            stream_ << indent() << "else ";
            dispatch_node(stmt->else_body().get());
        }
    }
}

void SystemVerilogCodeGen::stmt_code(ModuleInstantiationStmt* stmt) {
    stmt->verilog_ln = stream_.line_no();
    stream_ << indent() << stmt->target()->name;
    auto& params = stmt->target()->get_params();
    auto debug_info = stmt->port_debug();
    if (!params.empty()) {
        stream_ << " #(" << stream_.endl();
        indent_++;

        uint32_t count = 0;
        for (auto const& [name, param] : params) {
            stream_ << indent()
                    << ::format(
                           ".{0}({1}){2}", name, param->value_str(),
                           ++count == params.size() ? ")" : "," + std::string(1, stream_.endl()));
        }

        indent_--;
    }
    stream_ << " " << stmt->target()->instance_name << " (" << stream_.endl();
    indent_++;
    uint32_t count = 0;
    for (auto const& [internal, external] : stmt->port_mapping()) {
        if (generator_->debug && debug_info.find(internal) != debug_info.end()) {
            debug_info.at(internal)->verilog_ln = stream_.line_no();
        }
        const auto& end = count++ < stmt->port_mapping().size() - 1 ? ")," : ")";
        stream_ << indent() << "." << internal->to_string() << "(" << external->to_string() << end
                << stream_.endl();
    }
    stream_ << ");" << stream_.endl() << stream_.endl();
    indent_--;
}

void SystemVerilogCodeGen::stmt_code(SwitchStmt* stmt) {
    stream_ << indent() << "case (" << stmt->target()->to_string() << ")" << stream_.endl();
    indent_++;
    auto const& body = stmt->body();
    for (auto& [cond, stmt_blk] : body) {
        stream_ << indent() << (cond ? cond->to_string() : "default") << ": ";
        if (stmt_blk->empty()) {
            throw ::runtime_error(
                ::format("Switch statement condition {0} is empty!", cond->to_string()));
        } else {
            // directly output the code if the block only has 1 element
            if (stmt_blk->size() == 1) {
                skip_indent_ = true;
                dispatch_node((*stmt_blk)[0].get());
            } else {
                indent_++;
                dispatch_node(stmt_blk.get());
                indent_--;
            }
        }
    }

    indent_--;
    stream_ << indent() << "endcase" << stream_.endl();
}

std::string SystemVerilogCodeGen::get_port_str(Port* port) {
    std::vector<std::string> strs;
    strs.reserve(8);
    strs.emplace_back(port_dir_to_str(port->port_direction()));
    // we use logic for all inputs and outputs
    if (!port->is_packed()) {
        strs.emplace_back("logic");
    } else {
        auto ptr = reinterpret_cast<PortPacked*>(port);
        strs.emplace_back(ptr->packed_struct().struct_name);
    }
    if (port->is_signed) strs.emplace_back("signed");
    if (!port->is_packed()) strs.emplace_back(get_var_width_str(port));
    strs.emplace_back(port->name);

    if (port->size > 1) {
        strs.emplace_back(::format("[{0}:0]", port->size - 1));
    }
    return join(strs.begin(), strs.end(), " ");
}

}  // namespace kratos
