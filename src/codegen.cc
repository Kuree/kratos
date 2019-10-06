#include "codegen.hh"
#include <fmt/format.h>
#include "context.hh"
#include "except.hh"
#include "expr.hh"
#include "generator.hh"
#include "pass.hh"
#include "util.hh"

using fmt::format;

namespace kratos {

Stream::Stream(Generator* generator, SystemVerilogCodeGen* codegen)
    : generator_(generator), codegen_(codegen), line_no_(1) {}

Stream& Stream::operator<<(AssignStmt* stmt) {
    const auto& left = stmt->left()->to_string();
    const auto& right = stmt->right()->to_string();
    if (!stmt->comment.empty()) {
        (*this) << "// " << strip_newline(stmt->comment) << endl();
        (*this) << codegen_->indent();
    }

    if (generator_->debug) {
        stmt->verilog_ln = line_no_;
    }

    if (stmt->parent() == generator_) {
        // top level
        if (stmt->assign_type() != AssignmentType::Blocking)
            throw StmtException(
                ::format("Top level assignment for {0} <- {1} has to be blocking", left, right),
                {stmt->left().get(), stmt->right().get(), stmt});
        (*this) << ::format("assign {0} = {1};", left, right) << endl();
    } else {
        if (stmt->assign_type() == AssignmentType::Blocking)
            (*this) << ::format("{0}{1} = {2};", codegen_->indent(), left, right) << endl();
        else if (stmt->assign_type() == AssignmentType::NonBlocking)
            (*this) << ::format("{0}{1} <= {2};", codegen_->indent(), left, right) << endl();
        else
            throw StmtException(
                ::format("Top level assignment for {0} <- {1} has to be blocking", left, right),
                {stmt->left().get(), stmt->right().get(), stmt});
    }
    return *this;
}

Stream& Stream::operator<<(const std::pair<Port*, std::string>& port) {
    auto& [p, end] = port;
    if (!p->comment.empty())
        (*this) << codegen_->indent() << "// " << strip_newline(p->comment) << endl();
    if (generator_->debug) {
        p->verilog_ln = line_no_;
    }

    (*this) << codegen_->indent() << p->before_var_str() << SystemVerilogCodeGen::get_port_str(p)
            << p->after_var_str() << end << endl();

    return *this;
}

Stream& Stream::operator<<(const std::shared_ptr<Var>& var) {
    if (!var->comment.empty()) (*this) << "// " << strip_newline(var->comment) << endl();

    if (generator_->debug) {
        var->verilog_ln = line_no_;
    }

    // based on whether it's packed or not
    std::string type;
    if (var->is_packed()) {
        auto v = var->as<VarPacked>();
        type = v->packed_struct().struct_name;
    } else if (var->is_enum()) {
        auto v = var->as<EnumVar>();
        type = v->enum_type()->name;
    } else {
        type = "logic";
    }
    std::string format_str;
    if (var->size() > 1 && var->packed_array)
        format_str = "{0} {1} {4}{2} {3}{5};";
    else
        format_str = "{0} {1} {2} {3}{4}{5};";
    (*this) << var->before_var_str()
            << ::format(format_str, type, var->is_signed() ? "signed" : "",
                        var->is_enum() ? "" : SystemVerilogCodeGen::get_var_width_str(var.get()),
                        var->name, var->size() == 1 ? "" : ::format("[{0}:0]", var->size() - 1),
                        var->after_var_str())
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
    : SystemVerilogCodeGen(generator, "", "") {}

SystemVerilogCodeGen::SystemVerilogCodeGen(kratos::Generator* generator, std::string package_name,
                                           std::string header_name)
    : generator_(generator),
      package_name_(std::move(package_name)),
      header_include_name_(std::move(header_name)),
      stream_(generator, this) {
    // if it's an external file, we don't output anything
    if (generator->external()) return;

    // index the named blocks
    label_index_ = index_named_block();
}

void SystemVerilogCodeGen::output_module_def(Generator* generator) {  // output module definition
    // insert the header definition, if necessary
    if (!header_include_name_.empty()) {
        // two line indent
        stream_ << "`include \"" << header_include_name_ << "\"" << stream_.endl()
                << stream_.endl();
        // import everything
        stream_ << "import " << package_name_ << "::*;" << stream_.endl();
    }

    stream_ << ::format("module {0} ", generator->name);
    generate_parameters(generator);
    stream_ << indent() << "(" << stream_.endl();
    generate_ports(generator);
    stream_ << indent() << ");" << stream_.endl() << stream_.endl();
    generate_enums(generator);
    generate_variables(generator);
    generate_functions(generator);

    for (uint64_t i = 0; i < generator->stmts_count(); i++) {
        dispatch_node(generator->get_stmt(i).get());
    }

    stream_ << ::format("endmodule   // {0}", generator->name) << stream_.endl();
}

std::string SystemVerilogCodeGen::get_var_width_str(const Var* var) {
    std::string width;
    if (var->parametrized()) {
        width = ::format("{0}-1", var->param()->to_string());
    } else {
        width = std::to_string(var->var_width() - 1);
    }
    return var->var_width() > 1 && !var->is_packed() ? ::format("[{0}:0]", width) : "";
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
    if (!params.empty()) {
        stream_ << "#(";
        uint32_t count = 0;
        for (auto const& [name, param] : params) {
            stream_ << ::format("parameter {0} = {1}", name, param->value_str());
            if (++count < params.size()) stream_ << ", ";
        }
        stream_ << ")" << stream_.endl();
    }
}

void SystemVerilogCodeGen::generate_enums(kratos::Generator* generator) {
    auto enums = generator->get_enums();
    for (auto const& iter : enums) enum_code(iter.second.get());
}

void SystemVerilogCodeGen::generate_functions(kratos::Generator* generator) {
    auto funcs = generator->functions();
    for (auto const& iter : funcs) stmt_code(iter.second.get());
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
        throw StmtException(::format("Cannot codegen non-statement node. Got {0}",
                                     ast_type_to_string(node->ir_node_kind())),
                            {node});
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
    } else if (stmt_ptr->type() == StatementType ::FunctionalCall) {
        stmt_code(reinterpret_cast<FunctionCallStmt*>(node));
    } else if (stmt_ptr->type() == StatementType::Return) {
        stmt_code(reinterpret_cast<ReturnStmt*>(node));
    } else {
        throw StmtException("Not implemented", {node});
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
            throw StmtException("Cannot drive a module's input from itself",
                                {stmt, stmt->left().get(), stmt->right().get()});
        }
    }
    stream_ << stmt;
}

void SystemVerilogCodeGen::stmt_code(kratos::ReturnStmt* stmt) {
    if (generator_->debug) stmt->verilog_ln = stream_.line_no();
    stream_ << indent() << "return " << stmt->value()->to_string() << ";" << stream_.endl();
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
        case StatementBlockType::Function: {
            stmt_code(reinterpret_cast<FunctionStmtBlock*>(stmt));
            break;
        }
        case StatementBlockType::Initial: {
            stmt_code(reinterpret_cast<InitialStmtBlock*>(stmt));
        }
    }
}

void SystemVerilogCodeGen::stmt_code(SequentialStmtBlock* stmt) {
    // comment
    if (!stmt->comment.empty()) {
        stream_ << indent() << "// " << strip_newline(stmt->comment) << stream_.endl();
    }
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
    stream_ << stream_.endl() << "always_ff @(" << sensitive_list_str << ") begin"
            << block_label(stmt) << stream_.endl();
    indent_++;

    for (uint64_t i = 0; i < stmt->child_count(); i++) {
        dispatch_node(stmt->get_child(i));
    }

    indent_--;
    stream_ << indent() << "end" << block_label(stmt) << stream_.endl();
}

void SystemVerilogCodeGen::stmt_code(CombinationalStmtBlock* stmt) {
    // comment
    if (!stmt->comment.empty()) {
        stream_ << indent() << "// " << strip_newline(stmt->comment) << stream_.endl();
    }
    if (generator_->debug) {
        stmt->verilog_ln = stream_.line_no();
    }
    stream_ << "always_comb begin" << block_label(stmt) << stream_.endl();
    indent_++;

    for (uint64_t i = 0; i < stmt->child_count(); i++) {
        dispatch_node(stmt->get_child(i));
    }

    indent_--;
    stream_ << indent() << "end" << block_label(stmt) << stream_.endl();
}

void SystemVerilogCodeGen::stmt_code(kratos::InitialStmtBlock* stmt) {
    // comment
    if (!stmt->comment.empty()) {
        stream_ << indent() << "// " << strip_newline(stmt->comment) << stream_.endl();
    }
    if (generator_->debug) {
        stmt->verilog_ln = stream_.line_no();
    }

    stream_ << "initial begin" << block_label(stmt) << stream_.endl();
    indent_++;

    for (uint64_t i = 0; i < stmt->child_count(); i++) {
        dispatch_node(stmt->get_child(i));
    }

    indent_--;
    stream_ << indent() << "end" << block_label(stmt) << stream_.endl();
}

void SystemVerilogCodeGen::stmt_code(kratos::ScopedStmtBlock* stmt) {
    if (generator_->debug) {
        stmt->verilog_ln = stream_.line_no();
    }

    stream_ << "begin" << block_label(stmt) << stream_.endl();
    indent_++;

    for (uint64_t i = 0; i < stmt->child_count(); i++) {
        dispatch_node(stmt->get_child(i));
    }

    indent_--;
    stream_ << indent() << "end" << block_label(stmt) << stream_.endl();
}

void SystemVerilogCodeGen::stmt_code(kratos::FunctionStmtBlock* stmt) {
    // dpi is external module
    if (stmt->is_dpi()) return;
    if (generator_->debug) {
        stmt->verilog_ln = stream_.line_no();
    }
    std::string return_str = stmt->has_return_value() ? "" : "void ";
    stream_ << "function " << return_str << stmt->function_name() << "(" << stream_.endl();
    indent_++;
    uint64_t count = 0;
    auto ports = stmt->ports();
    // if the ordering is specified, use the ordering
    // otherwise use the default map ordering, which is sorted alphabetically
    std::vector<std::string> port_names;
    port_names.reserve(ports.size());
    auto ordering = stmt->port_ordering();
    for (auto const& iter : ports) port_names.emplace_back(iter.first);
    if (!ordering.empty()) {
        if (ordering.size() != ports.size())
            throw InternalException("Port ordering size mismatches ports");
        // sort the list
        std::sort(port_names.begin(), port_names.end(), [&](auto const& lhs, auto const& rhs) {
            return ordering.at(lhs) < ordering.at(rhs);
        });
    }
    for (auto const& port_name : port_names) {
        auto port = ports.at(port_name).get();
        if (generator_->debug) port->verilog_ln = stream_.line_no();
        stream_ << indent() << get_port_str(port);
        if (++count != ports.size())
            stream_ << "," << stream_.endl();
        else
            stream_ << stream_.endl() << ");" << stream_.endl();
    }
    indent_--;

    stream_ << "begin" << stream_.endl();
    indent_++;
    for (uint64_t i = 0; i < stmt->child_count(); i++) {
        dispatch_node(stmt->get_child(i));
    }
    indent_--;
    stream_ << indent() << "end" << stream_.endl() << "endfunction" << stream_.endl();
}

void SystemVerilogCodeGen::stmt_code(IfStmt* stmt) {
    if (generator_->debug) {
        stmt->verilog_ln = stream_.line_no();
        if (stmt->predicate()->verilog_ln == 0) stmt->predicate()->verilog_ln = stream_.line_no();
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
    // comment
    if (!stmt->comment.empty()) {
        stream_ << indent() << "// " << strip_newline(stmt->comment) << stream_.endl();
    }
    stmt->verilog_ln = stream_.line_no();
    stream_ << indent() << stmt->target()->name;
    auto& params = stmt->target()->get_params();
    auto debug_info = stmt->port_debug();
    if (!params.empty()) {
        std::vector<std::string> param_names;
        param_names.reserve(params.size());
        for (auto const& iter : params) {
            param_names.emplace_back(iter.first);
        }
        std::sort(param_names.begin(), param_names.end());
        stream_ << " #(" << stream_.endl();
        indent_++;

        uint32_t count = 0;
        for (auto const& name : param_names) {
            auto const& param = params.at(name);
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
    std::vector<std::pair<std::shared_ptr<Var>, std::shared_ptr<Var>>> ports;
    auto const& mapping = stmt->port_mapping();
    ports.reserve(mapping.size());
    for (auto const& iter : mapping) ports.emplace_back(iter);
    std::sort(ports.begin(), ports.end(),
              [](const auto& lhs, const auto& rhs) { return lhs.first->name < rhs.first->name; });
    for (auto const& [internal, external] : ports) {
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
    stream_ << indent() << "unique case (" << stmt->target()->to_string() << ")" << stream_.endl();
    indent_++;
    auto const& body = stmt->body();
    std::vector<std::shared_ptr<Const>> conds;
    conds.reserve(body.size());
    for (auto const& iter : body) {
        if (iter.first) conds.emplace_back(iter.first);
    }
    std::sort(conds.begin(), conds.end(),
              [](const auto& lhs, const auto& rhs) { return lhs->value() < rhs->value(); });
    if (body.find(nullptr) != body.end()) conds.emplace_back(nullptr);

    for (auto& cond : conds) {
        auto& stmt_blk = body.at(cond);
        stream_ << indent() << (cond ? cond->to_string() : "default") << ": ";
        if (stmt_blk->empty() && cond) {
            throw VarException(
                ::format("Switch statement condition {0} is empty!", cond->to_string()),
                {stmt, cond.get()});
        } else if (stmt_blk->empty() && !cond) {
            //  empty default case
            stream_ << "begin end" << stream_.endl();
        } else {
            // directly output the code if the block only has 1 element
            if (stmt_blk->size() == 1 && label_index_.find(stmt_blk.get()) == label_index_.end()) {
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

void SystemVerilogCodeGen::stmt_code(kratos::FunctionCallStmt* stmt) {
    // since this is a statement, we don't allow it has return value
    // need to use it as a function call expr instead
    if (stmt->parent()->ir_node_kind() != IRNodeKind::StmtKind) {
        throw StmtException("Function call statement cannot be used in top level", {stmt});
    }
    if (generator_->debug) stmt->verilog_ln = stream_.line_no();
    stream_ << indent() << stmt->var()->to_string();

    stream_ << ";" << stream_.endl();
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
    if (port->is_signed()) strs.emplace_back("signed");
    if (port->size() > 1 && port->packed_array) {
        strs.emplace_back(::format("[{0}:0]", port->size() - 1));
    }
    if (!port->is_packed()) strs.emplace_back(get_var_width_str(port));
    strs.emplace_back(port->name);

    if (port->size() > 1 && !port->packed_array) {
        strs.emplace_back(::format("[{0}:0]", port->size() - 1));
    }
    return join(strs.begin(), strs.end(), " ");
}

std::unordered_map<StmtBlock*, std::string> SystemVerilogCodeGen::index_named_block() {
    std::unordered_map<StmtBlock*, std::string> result;
    auto names = generator_->named_blocks_labels();
    result.reserve(names.size());
    for (auto const& name : names) {
        result.emplace(generator_->get_named_block(name).get(), name);
    }
    return result;
}

std::string SystemVerilogCodeGen::block_label(kratos::StmtBlock* stmt) {
    if (label_index_.find(stmt) != label_index_.end())
        return " :" + label_index_.at(stmt);
    else
        return "";
}

void SystemVerilogCodeGen::enum_code(kratos::Enum* enum_) {
    std::string logic_str = enum_->width() == 1 ? "" : ::format("[{0}:0]", enum_->width() - 1);
    stream_ << indent() << "typedef enum logic" << logic_str << " {" << stream_.endl();
    uint32_t count = 0;
    indent_++;
    for (auto& [name, c] : enum_->values) {
        if (generator_->debug) {
            c->verilog_ln = stream_.line_no();
        }
        stream_ << indent() << name << " = " << c->value_string();
        if (++count != enum_->values.size()) stream_ << ",";
        stream_ << stream_.endl();
    }
    indent_--;
    stream_ << indent() << "} " << enum_->name << ";" << stream_.endl();
}

}  // namespace kratos
