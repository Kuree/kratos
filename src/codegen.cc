#include "codegen.hh"

#include <fmt/format.h>

#include <mutex>

#include "context.hh"
#include "except.hh"
#include "expr.hh"
#include "generator.hh"
#include "graph.hh"
#include "interface.hh"
#include "pass.hh"
#include "tb.hh"
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

    std::string prefix;
    std::string eq;

    if (stmt->parent() == generator_) {
        // top level
        if (stmt->assign_type() != AssignmentType::Blocking)
            throw StmtException(
                ::format("Top level assignment for {0} <- {1} has to be blocking", left, right),
                {stmt->left(), stmt->right(), stmt});
        prefix = "assign ";
        eq = "=";
        /*
        (*this) << ::format("assign {0} = ", left);
        auto wrapped_right = line_wrap(right, 100);
        for (uint64_t i = 0; i < wrapped_right.size() - 1; i++) {
            // compute new indent
            auto new_indent = codegen_->indent() + "    ";
            (*this) << wrapped_right[i] << endl();
        }
        (*this) << wrapped_right.back() << ";" << endl();
         */
    } else {
        prefix = codegen_->indent();
        if (stmt->assign_type() == AssignmentType::Blocking)
            eq = "=";
        else if (stmt->assign_type() == AssignmentType::NonBlocking)
            eq = "<=";
        else
            throw StmtException(
                ::format("Top level assignment for {0} <- {1} has to be blocking", left, right),
                {stmt->left(), stmt->right(), stmt});
    }
    (*this) << prefix << left << " " << eq << " ";  //<< right << ";" << endl();
    auto right_wrapped = line_wrap(right, 80);
    (*this) << right_wrapped[0];
    for (uint64_t i = 1; i < right_wrapped.size(); i++) {
        // compute new indent
        (*this) << endl();
        auto new_indent = codegen_->indent() + "    ";
        (*this) << new_indent << right_wrapped[i];
    }
    (*this) << ";" << endl();
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

std::string Stream::get_var_decl(kratos::Var* var) {
    // based on whether it's packed or not
    std::string type;
    if (var->is_struct()) {
        auto v = var->as<VarPackedStruct>();
        type = v->packed_struct().struct_name;
    } else if (var->is_enum()) {
        auto v = dynamic_cast<EnumType*>(var);
        if (!v) throw InternalException("Unable to resolve var to enum type");
        type = v->enum_type()->name;
    } else {
        type = "logic";
    }

    std::vector<std::string> str = {type};
    if (var->is_signed()) str.emplace_back("signed");
    std::string var_width = SystemVerilogCodeGen::get_var_width_str(var);
    if (var->size().front() > 1 || var->size().size() > 1 || var->explicit_array()) {
        // it's an array
        if (var->is_packed()) {
            std::string array_str;
            for (auto const& w : var->size())
                array_str.append(SystemVerilogCodeGen::get_width_str(w));
            if (!var_width.empty()) array_str.append(var_width);
            str.emplace_back(array_str);
            str.emplace_back(var->name);
        } else {
            if (!var_width.empty()) str.emplace_back(var_width);
            str.emplace_back(var->name);
            std::string array_str;
            for (auto const& w : var->size())
                array_str.append(SystemVerilogCodeGen::get_width_str(w));
            str.emplace_back(array_str);
        }
    } else {
        // scalar
        if (!var_width.empty() && !var->is_enum()) str.emplace_back(var_width);
        str.emplace_back(var->name);
    }

    auto var_str = string::join(str.begin(), str.end(), " ");
    return var_str;
}

Stream& Stream::operator<<(const std::shared_ptr<Var>& var) {
    if (!var->comment.empty()) (*this) << "// " << strip_newline(var->comment) << endl();

    if (generator_->debug) {
        var->verilog_ln = line_no_;
    }

    auto var_str = get_var_decl(var.get());

    (*this) << var->before_var_str() << var_str << var->after_var_str() << ";" << endl();
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
    if (generator->debug) generator->verilog_ln = stream_.line_no();
    stream_ << ::format("module {0} ", generator->name);
    generate_parameters(generator);
    stream_ << indent() << "(" << stream_.endl();
    generate_ports(generator);
    stream_ << indent() << ");" << stream_.endl() << stream_.endl();
    generate_enums(generator);
    generate_variables(generator);
    generate_interface(generator);
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
    return var->var_width() > 1 && !var->is_struct() ? ::format("[{0}:0]", width) : "";
}

std::string SystemVerilogCodeGen::get_width_str(uint32_t width) {
    return ::format("[{0}:0]", width - 1);
}

void SystemVerilogCodeGen::generate_ports(Generator* generator) {
    indent_++;
    // sort the names
    auto& port_names_set = generator->get_port_names();
    std::vector<std::string> port_names(port_names_set.begin(), port_names_set.end());
    std::sort(port_names.begin(), port_names.end());
    std::unordered_set<std::string> interface_name;

    std::vector<Port*> ports;
    ports.reserve(port_names.size());

    std::vector<std::string> v95_names;
    v95_names.reserve(port_names.size());

    std::vector<std::pair<std::string, std::string>> interface_names;
    interface_names.reserve(port_names.size() / 2);

    for (const auto& port_name : port_names) {
        auto port = generator->get_port(port_name);
        if (!port->is_interface()) {
            ports.emplace_back(port.get());
        } else {
            auto port_interface = port->as<InterfacePort>();
            auto ref = port_interface->interface();
            auto const& ref_name = ref->name();
            // only print out interface def once
            if (interface_name.find(ref_name) == interface_name.end()) {
                auto const& def_name = ref->definition()->def_name();
                interface_names.emplace_back(std::make_pair(def_name, ref_name));
                interface_name.emplace(ref_name);
            }
        }
    }

    uint64_t count = 0;
    uint64_t size = interface_names.size() + ports.size();
    for (auto const& [def, ref] : interface_names) {
        count++;
        stream_ << indent() << def << " " << ref;
        if (count != size) stream_ << ",";
        stream_ << stream_.endl();
    }
    for (auto const& port : ports) {
        count++;
        auto end = count == size ? "" : ",";
        stream_ << std::make_pair(port, end);
    }
    indent_--;
}

void SystemVerilogCodeGen::generate_variables(Generator* generator) {
    auto const& vars = generator->get_vars();
    for (auto const& var_name : vars) {
        auto const& var = generator->get_var(var_name);
        if (var->type() == VarType::Base && !var->is_interface()) {
            stream_ << var;
        }
    }
}

void SystemVerilogCodeGen::generate_parameters(Generator* generator) {
    auto& params = generator->get_params();
    if (!params.empty()) {
        stream_ << "#(parameter ";
        uint32_t count = 0;
        for (auto const& [name, param] : params) {
            stream_ << ::format("{0} = {1}", name, param->value_str());
            if (++count < params.size()) stream_ << ", ";
        }
        stream_ << ")" << stream_.endl();
    }
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
    } else if (stmt_ptr->type() == StatementType::Assert) {
        stmt_code(reinterpret_cast<AssertBase*>(node));
    } else if (stmt_ptr->type() == StatementType::Comment) {
        stmt_code(reinterpret_cast<CommentStmt*>(node));
    } else if (stmt_ptr->type() == StatementType::InterfaceInstantiation) {
        // do nothing
    } else if (stmt_ptr->type() == StatementType::RawString) {
        stmt_code(reinterpret_cast<RawStringStmt*>(node));
    } else if (stmt_ptr->type() == StatementType::For) {
        stmt_code(reinterpret_cast<ForStmt*>(node));
    } else {
        throw StmtException("Not implemented", {node});
    }
}

void SystemVerilogCodeGen::stmt_code(AssignStmt* stmt) {
    if (stmt->left()->type() == VarType::PortIO) {
        auto port = stmt->left()->as<Port>();
        if (port->port_direction() == PortDirection::In &&
            stmt->left()->generator() == generator_ &&
            stmt->right()->type() != VarType::ConstValue) {
            throw StmtException("Cannot drive a module's input from itself",
                                {stmt, stmt->left(), stmt->right()});
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
            break;
        }
        case StatementBlockType::Latch: {
            stmt_code(reinterpret_cast<LatchStmtBlock*>(stmt));
            break;
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
    std::string sensitive_list_str =
        string::join(sensitive_list.begin(), sensitive_list.end(), ", ");
    stream_ << stream_.endl() << "always_ff @(" << sensitive_list_str << ") begin"
            << block_label(stmt) << stream_.endl();
    indent_++;

    for (uint64_t i = 0; i < stmt->size(); i++) {
        dispatch_node(stmt->get_child(i));
    }

    indent_--;
    stream_ << indent() << "end" << block_label(stmt) << stream_.endl();
}

void SystemVerilogCodeGen::block_code(const std::string& syntax_name, kratos::StmtBlock* stmt) {
    // comment
    if (!stmt->comment.empty()) {
        stream_ << indent() << "// " << strip_newline(stmt->comment) << stream_.endl();
    }
    if (generator_->debug) {
        stmt->verilog_ln = stream_.line_no();
    }
    stream_ << syntax_name << " begin" << block_label(stmt) << stream_.endl();
    indent_++;

    for (uint64_t i = 0; i < stmt->size(); i++) {
        dispatch_node(stmt->get_child(i));
    }

    indent_--;
    stream_ << indent() << "end" << block_label(stmt) << stream_.endl();
}

void SystemVerilogCodeGen::stmt_code(CombinationalStmtBlock* stmt) {
    block_code("always_comb", stmt);
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

    for (uint64_t i = 0; i < stmt->size(); i++) {
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

void SystemVerilogCodeGen::stmt_code(AssertBase* stmt) {
    if (stmt->assert_type() == AssertType::AssertValue) {
        auto st = reinterpret_cast<AssertValueStmt*>(stmt);
        stream_ << indent() << "assert (" << st->value()->handle_name(stmt->generator_parent())
                << ")";
        if (st->else_()) {
            stream_ << " else ";
            // turn off the indent
            auto temp = indent_;
            indent_ = 0;
            dispatch_node(st->else_().get());
            indent_ = temp;
            // dispatch code will close the ;
        } else {
            stream_ << ";" << stream_.endl();
        }
    } else {
        auto st = stmt->as<AssertPropertyStmt>();
        stmt_code(st.get());
    }
}

void SystemVerilogCodeGen::stmt_code(AssertPropertyStmt* stmt) {
    auto property = stmt->property();
    stream_ << indent() << "property " << property->property_name() << ";" << stream_.endl();
    increase_indent();
    auto edge = property->edge();
    auto seq = property->sequence();
    // automatically determine the clock, only if it's safe to do so (only one clock in the
    // design
    if (!edge.first && seq->next()) {
        std::vector<Var*> clk_vars;
        // try to determine the clock
        // it's concurrent property, we have to have a clock
        auto generator = stmt->generator_parent();
        {
            auto clk_ports = generator->get_ports(PortType::Clock);
            if (clk_ports.size() == 1) {
                // that's it
                clk_vars.emplace_back(generator->get_port(clk_ports.front()).get());
            } else {
                for (auto const& port_name : clk_ports) {
                    clk_vars.emplace_back(generator->get_port(port_name).get());
                }
            }
        }
        if (clk_vars.empty()) {
            // there might be some casted types, typically in test bench
            // we need to source for connected modules to see what they are connected to
            auto children = generator->get_child_generators();
            for (auto const& gen : children) {
                auto clks = gen->get_ports(PortType::Clock);
                for (auto const& clk_name : clks) {
                    auto clk = gen->get_port(clk_name);
                    auto source = clk->sources();
                    for (auto const& assign : source) {
                        auto src_var = assign->right();
                        if (src_var->generator() == generator) {
                            if (src_var->type() == VarType::BaseCasted) {
                                // only casted to clock
                                auto casted = src_var->as<VarCasted>();
                                if (casted->cast_type() == VarCastType::Clock)
                                    clk_vars.emplace_back(src_var);
                            }
                        }
                    }
                }
            }
        }

        if (clk_vars.size() == 1) {
            edge.first = clk_vars[0];
            edge.second = BlockEdgeType::Posedge;
        } else {
            // next is not null but edge is not set
            throw StmtException(::format("Clock edge not set for sequence {0}", seq->to_string()),
                                {stmt});
        }
    }
    if (edge.first) {
        auto const& [var, type] = edge;
        stream_ << indent()
                << ::format("@({0} {1}) ", type == BlockEdgeType::Posedge ? "posedge" : "negedge",
                            var->handle_name(true));
    }
    stream_ << seq->to_string() << ";" << stream_.endl();
    decrease_indent();
    stream_ << indent() << "endproperty" << stream_.endl();

    // put assert here
    stream_ << indent() << "assert property (" << property->property_name() << ");"
            << stream_.endl();
}

void SystemVerilogCodeGen::stmt_code(CommentStmt* stmt) {
    auto const& comments = stmt->comments();
    for (auto const& comment : comments) {
        stream_ << indent() << "// " << comment << stream_.endl();
    }
}

void SystemVerilogCodeGen::stmt_code(RawStringStmt* stmt) {
    auto const& stmts = stmt->stmts();
    for (auto const& line : stmts) {
        // we assume it's already been processed with new lines
        stream_ << indent() << line << stream_.endl();
    }
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
        auto first_stmt = else_body->empty() ? nullptr : else_body->get_stmt(0);
        bool skip = else_body->size() == 1 && (first_stmt->type() == StatementType::Assign ||
                                               first_stmt->type() == StatementType::If ||
                                               first_stmt->type() == StatementType::Return);
        if (skip) {
            stream_ << indent() << "else ";
            skip_indent_ = true;
            else_body->verilog_ln = stream_.line_no();
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
            auto value = param->value_str();
            if (param->parent_param()) {
                auto p = param->parent_param();
                // checking on parameter parent
                auto p_gen = p->generator();
                if (p_gen != stmt->generator_parent()) {
                    throw VarException(
                        ::format("{0}.{1} is not declared in generator {2}", p_gen->name, p->name,
                                 stmt->generator_parent()->name),
                        {stmt, p_gen, p});
                }
                value = p->to_string();
            }
            stream_ << indent()
                    << ::format(
                           ".{0}({1}){2}", name, value,
                           ++count == params.size() ? ")" : "," + std::string(1, stream_.endl()));
        }

        indent_--;
    }
    stream_ << " " << stmt->target()->instance_name;
    generate_port_interface(stmt);
}

void SystemVerilogCodeGen::stmt_code(kratos::InterfaceInstantiationStmt* stmt) {
    // comment
    if (!stmt->comment.empty()) {
        stream_ << indent() << "// " << strip_newline(stmt->comment) << stream_.endl();
    }
    stmt->verilog_ln = stream_.line_no();
    auto const& interface = stmt->interface();
    stream_ << indent() << interface->definition()->def_name() << " " << interface->name();
    // TODO: allow parametrization
    generate_port_interface(stmt);
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

void SystemVerilogCodeGen::stmt_code(kratos::ForStmt* stmt) {
    // for loop
    if (generator_->debug) stmt->verilog_ln = stream_.line_no();
    auto iter = stmt->get_iter_var();
    stream_ << indent() << "for (int " << (iter->is_signed() ? " " : "unsigned ")
            << iter->to_string() << " = ";
    stream_ << ::format("{0}", stmt->start()) << "; " << iter->to_string()
            << (stmt->end() > stmt->start() ? " < " : " > ") ;
    stream_ << ::format("{0}", stmt->end()) << "; "
            << iter->to_string() << (stmt->step() > 0 ? " += " : " -= ");
    stream_ << ::format("{0}", std::abs(stmt->step())) << ") ";
    indent_++;
    dispatch_node(stmt->get_loop_body().get());
    indent_--;
}

void SystemVerilogCodeGen::stmt_code(LatchStmtBlock* stmt) { block_code("always_latch", stmt); }

std::string SystemVerilogCodeGen::get_port_str(Port* port) {
    std::vector<std::string> strs;
    strs.reserve(8);
    strs.emplace_back(port_dir_to_str(port->port_direction()));
    // we use logic for all inputs and outputs
    if (!port->is_struct() && !port->is_enum()) {
        strs.emplace_back("logic");
    } else if (port->is_enum()) {
        auto enum_def = dynamic_cast<EnumPort*>(port);
        if (!enum_def) throw InternalException("Unable to convert port to enum_def");
        strs.emplace_back(enum_def->enum_type()->name);
    } else {
        auto ptr = reinterpret_cast<PortPackedStruct*>(port);
        strs.emplace_back(ptr->packed_struct().struct_name);
    }
    if (port->is_signed()) strs.emplace_back("signed");
    if ((port->size().front() > 1 || port->size().size() > 1 || port->explicit_array()) &&
        port->is_packed()) {
        std::string str;
        for (auto const& w : port->size()) str.append(get_width_str(w));
        strs.emplace_back(str);
    }
    if (!port->is_struct() && !port->is_enum()) {
        auto const& var_width_str = get_var_width_str(port);
        if (!var_width_str.empty()) strs.emplace_back(var_width_str);
    }
    strs.emplace_back(port->name);

    if ((port->size().front() > 1 || port->size().size() > 1 || port->explicit_array()) &&
        !port->is_packed()) {
        std::string str;
        for (auto const& w : port->size()) str.append(get_width_str(w));
        strs.emplace_back(str);
    }
    return string::join(strs.begin(), strs.end(), " ");
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

std::string SystemVerilogCodeGen::enum_code(kratos::Enum* enum_) {
    Stream stream_(nullptr, nullptr);
    enum_code_(stream_, enum_, false);
    return stream_.str();
}

void SystemVerilogCodeGen::enum_code_(kratos::Enum* enum_) {
    enum_code_(stream_, enum_, generator_->debug);
}

void SystemVerilogCodeGen::generate_enums(kratos::Generator* generator) {
    auto enums = generator->get_enums();
    for (auto const& iter : enums) enum_code_(iter.second.get());
}

void SystemVerilogCodeGen::generate_port_interface(kratos::InstantiationStmt* stmt) {
    if (stmt->port_mapping().empty()) {
        stream_ << "();" << stream_.endl();
        return;
    }
    stream_ << " (" << stream_.endl();
    indent_++;
    std::vector<std::pair<Port*, Var*>> ports;
    auto const& mapping = stmt->port_mapping();
    ports.reserve(mapping.size());
    for (auto const& iter : mapping) ports.emplace_back(iter);
    std::sort(ports.begin(), ports.end(),
              [](const auto& lhs, const auto& rhs) { return lhs.first->name < rhs.first->name; });
    auto debug_info = stmt->port_debug();
    std::unordered_map<std::string, std::string> interface_names;
    std::vector<std::pair<std::string, std::string>> connections;
    connections.reserve(ports.size());
    for (auto const& [internal, external] : ports) {
        if (generator_->debug && debug_info.find(internal) != debug_info.end()) {
            debug_info.at(internal)->verilog_ln = stream_.line_no();
        }
        std::string internal_name;
        std::string external_name;
        if (stmt->instantiation_type() == InstantiationStmt::InstantiationType::Interface) {
            internal_name = internal->name;
            external_name = external->name;
        } else {
            // module
            if (!internal->is_interface()) {
                internal_name = internal->to_string();
                external_name = external->to_string();
            } else {
                // we assume the interface connectivity has been checked
                // internal has to be an interface
                auto internal_interface = internal->as<InterfacePort>();
                if (!internal_interface) throw InternalException("Unable to cast port");
                auto internal_def = internal_interface->interface();
                internal_name = internal_def->name();
                if (internal_def->definition()->is_modport()) {
                    // it's a mod port
                    // get the mod port name
                    auto mod_port_name = internal_def->definition()->name();
                    external_name = external->base_name();
                    // FIXME: this is a little bit hacky here
                    if (external_name.find('.') == std::string::npos)
                        external_name = ::format("{0}.{1}", external_name, mod_port_name);
                } else {
                    external_name = external->base_name();
                }

                if (interface_names.find(internal_name) != interface_names.end()) {
                    if (interface_names.at(internal_name) != external_name) {
                        throw StmtException(
                            ::format("{0} and {1} are not from the same interface definition",
                                     internal->handle_name(), external->handle_name()),
                            {internal, external});
                    }
                    continue;
                }
                interface_names.emplace(internal_name, external_name);
            }
        }
        connections.emplace_back(std::make_pair(internal_name, external_name));
    }
    for (uint64_t i = 0; i < connections.size(); i++) {
        auto const& [internal_name, external_name] = connections[i];
        stream_ << indent() << "." << internal_name << "(" << external_name << ")";
        if (i != connections.size() - 1)
            stream_ << "," << stream_.endl();
        else
            stream_ << stream_.endl();
    }
    stream_ << ");" << stream_.endl() << stream_.endl();
    indent_--;
}

void SystemVerilogCodeGen::generate_interface(Generator* generator) {
    uint64_t stmt_count = generator->stmts_count();
    for (uint64_t i = 0; i < stmt_count; i++) {
        auto stmt = generator->get_stmt(i);
        if (stmt->type() == StatementType::InterfaceInstantiation) {
            auto s = stmt->as<InterfaceInstantiationStmt>();
            stmt_code(s.get());
        }
    }
}

void SystemVerilogCodeGen::enum_code_(kratos::Stream& stream_, kratos::Enum* enum_, bool debug) {
    std::string logic_str = enum_->width() == 1 ? "" : ::format("[{0}:0]", enum_->width() - 1);
    stream_ << "typedef enum logic" << logic_str << " {" << stream_.endl();
    uint32_t count = 0;
    auto const indent = "  ";
    // sort it by the values
    std::vector<std::string> names;
    names.reserve(enum_->values.size());
    for (auto const& iter : enum_->values) names.emplace_back(iter.first);
    std::sort(names.begin(), names.end(), [&](const auto& a, const auto& b) {
        return enum_->values.at(a)->value() < enum_->values.at(b)->value();
    });
    for (auto const& name : names) {
        auto& c = enum_->values.at(name);
        if (debug) {
            c->verilog_ln = stream_.line_no();
        }
        stream_ << indent << name << " = " << c->value_string();
        if (++count != enum_->values.size()) stream_ << ",";
        stream_ << stream_.endl();
    }
    stream_ << "} " << enum_->name << ";" << stream_.endl();
}

std::string create_stub(Generator* top) {
    // we can't generate verilog-95 directly from the codegen here here
    auto port_names = top->get_port_names();
    Generator gen(nullptr, top->name);
    for (auto const& port_name : port_names) {
        auto port = top->get_port(port_name);
        auto& p = gen.port(port->port_direction(), port_name, port->var_width(), port->size(),
                           port->port_type(), port->is_signed());
        p.set_is_packed(port->is_packed());
    }
    // that's it
    // now outputting the stream
    auto res = generate_verilog(&gen);
    return res.at(top->name);
}

class InterfaceVisitor : public IRVisitor {
public:
    void visit(Generator* generator) override {
        uint64_t stmt_count = generator->stmts_count();
        for (uint64_t i = 0; i < stmt_count; i++) {
            auto stmt = generator->get_stmt(i);
            if (stmt->type() == StatementType::InterfaceInstantiation) {
                visit(stmt->as<InterfaceInstantiationStmt>().get());
            }
        }
    }
    void visit(InterfaceInstantiationStmt* stmt) override {
        auto def = stmt->interface()->definition();
        lock_.lock();
        if (interfaces_.find(def->def_name()) == interfaces_.end()) {
            interfaces_.emplace(def->def_name(), std::make_pair(stmt, stmt->interface()));
            lock_.unlock();
        } else {
            // making sure they are the same
            auto const& [ref_stmt, ref_interface] = interfaces_.at(def->def_name());
            auto ref_def = ref_interface->definition();
            lock_.unlock();
            auto const& ports = def->ports();
            if (ref_def->ports() != ports)
                throw UserException(
                    ::format("{0}.{1}'s interface differs from {2}.{3}'s",
                             stmt->generator_parent()->handle_name(), def->def_name(),
                             ref_stmt->generator_parent()->handle_name(), ref_def->def_name()));
            for (auto const& port_name : ports) {
                if (def->port(port_name) != ref_def->port(port_name))
                    throw UserException(
                        ::format("{0}.{1}'s interface differs from {2}.{3}'s",
                                 stmt->generator_parent()->handle_name(), def->def_name(),
                                 ref_stmt->generator_parent()->handle_name(), ref_def->def_name()));
            }
            // same var as well
            auto const& vars = def->vars();
            if (ref_def->vars() != vars)
                throw UserException(
                    ::format("{0}.{1}'s interface differs from {2}.{3}'s",
                             stmt->generator_parent()->handle_name(), def->def_name(),
                             ref_stmt->generator_parent()->handle_name(), ref_def->def_name()));
            for (auto const& port_name : vars) {
                if (def->var(port_name) != ref_def->var(port_name))
                    throw UserException(
                        ::format("{0}.{1}'s interface differs from {2}.{3}'s",
                                 stmt->generator_parent()->handle_name(), def->def_name(),
                                 ref_stmt->generator_parent()->handle_name(), ref_def->def_name()));
            }
        }
    }

    const std::unordered_map<std::string,
                             std::pair<InterfaceInstantiationStmt*, const InterfaceRef*>>&
    interfaces() const {
        return interfaces_;
    }

private:
    std::unordered_map<std::string, std::pair<InterfaceInstantiationStmt*, const InterfaceRef*>>
        interfaces_;
    std::mutex lock_;
};

std::map<std::string, std::string> extract_interface_info(Generator* top) {
    InterfaceVisitor visitor;
    visitor.visit_generator_root_p(top);
    auto defs = visitor.interfaces();
    std::map<std::string, std::string> result;
    const std::string indent = "  ";
    for (auto const& [interface_name, def] : defs) {
        auto i_ref = def.second;
        auto const& i_def = i_ref->definition();
        if (i_def->is_modport())
            // don't generate mod port definition
            continue;
        std::stringstream stream;
        stream << "interface " << interface_name;
        if (!i_def->ports().empty()) {
            stream << "(" << std::endl;
            auto port_names = i_def->ports();
            uint32_t i = 0;
            for (auto const& port_name : port_names) {
                auto p = &i_ref->port(port_name);
                stream << indent << SystemVerilogCodeGen::get_port_str(p);
                if (i++ == port_names.size() - 1)
                    stream << std::endl;
                else
                    stream << "," << std::endl;
            }
            stream << ");" << std::endl;
        } else {
            stream << ";" << std::endl;
        }
        // output vars
        auto const& vars = i_def->vars();
        for (auto const& var_name : vars) {
            auto v = &i_ref->var(var_name);
            stream << indent << Stream::get_var_decl(v) << ";" << std::endl;
        }

        // modports
        auto interface_definition = std::static_pointer_cast<InterfaceDefinition>(i_def);
        auto const& mod_ports = interface_definition->mod_ports();
        for (auto const& [mod_name, mod_port] : mod_ports) {
            stream << indent << "modport " << mod_name << "(";
            auto const& ports = mod_port->ports();
            if (ports.empty()) throw UserException(::format("{0} is empty", mod_name));
            auto const& inputs = mod_port->inputs();
            auto const& outputs = mod_port->outputs();
            uint32_t count = 0;
            for (auto const& name : inputs) {
                stream << "input " << name;
                if (++count != ports.size()) stream << ", ";
            }
            for (auto const& name : outputs) {
                stream << "output " << name;
                if (++count != ports.size()) stream << ", ";
            }
            stream << ");" << std::endl;
        }
        stream << "endinterface" << std::endl;
        result.emplace(interface_name, stream.str());
    }
    return result;
}

Generator& create_wrapper_flatten(Generator* top, const std::string& wrapper_name) {
    auto& gen = top->context()->generator(wrapper_name);
    gen.add_child_generator(top->instance_name, top->shared_from_this());
    auto const& ports = top->get_port_names();
    for (auto const& port_name : ports) {
        auto p = top->get_port(port_name);
        if (p->size().size() == 1 && p->size()[0] == 1) {
            // this is a normal wire
            auto& new_port = gen.port(*p);
            if (p->port_direction() == PortDirection::In) {
                gen.add_stmt(p->assign(new_port, AssignmentType::Blocking));
            } else {
                gen.add_stmt(new_port.assign(p, AssignmentType::Blocking));
            }
        } else {
            // need to flatten the array
            auto slices = get_flatten_slices(p.get());
            // create port for them based on the slice
            for (auto const& slice : slices) {
                std::string name = port_name;
                for (auto const& s : slice) name = ::format("{0}_{1}", name, s);
                auto slice_port = &(*p)[slice[0]];
                for (uint64_t i = 1; i < slice.size(); i++) slice_port = &(*slice_port)[slice[i]];
                if (slice_port->size().size() != 1 || slice_port->size()[0] != 1)
                    throw InternalException("Unable to slice ports when flattening");
                auto& new_port = gen.port(p->port_direction(), name, slice_port->var_width());
                if (p->port_direction() == PortDirection::In) {
                    gen.add_stmt(slice_port->assign(new_port, AssignmentType::Blocking));
                } else {
                    gen.add_stmt(
                        new_port.assign(slice_port->shared_from_this(), AssignmentType::Blocking));
                }
            }
        }
    }
    return gen;
}

std::pair<std::string, uint32_t> generate_sv_package_header(Generator* top,
                                                            const std::string& package_name,
                                                            bool include_guard) {
    Stream stream(nullptr, nullptr);
    // we will write out the dpi and struct ones to the header file
    // this is to ensure everything will be set if this function is called
    // output the guard
    auto struct_info = extract_struct_info(top);
    auto dpi_info = extract_dpi_function(top, true);
    auto enum_info = extract_enum_info(top);
    auto interface_info = extract_interface_info(top);
    if (include_guard) {
        // output the guard
        std::string guard_name = "kratos_" + package_name;
        // make it upper case
        std::for_each(guard_name.begin(), guard_name.end(),
                      [](char& c) { c = static_cast<char>(::toupper(c)); });
        stream << "`ifndef " << guard_name << stream.endl();
        stream << "`define " << guard_name << stream.endl();
        // package header
        stream << "package " << package_name << ";" << stream.endl();
    }

    // all the information list
    auto info_list = {dpi_info, struct_info, enum_info, interface_info};
    for (auto const& info : info_list) {
        for (auto const& iter : info) {
            auto def = iter.second;
            // split on new line to replace with the stream new line so that we can track
            // the new lines
            auto lines = string::get_tokens(def, "\n");
            for (auto const& line : lines) {
                stream << line << stream.endl();
            }
            stream << stream.endl();
        }
    }

    // closing
    stream << "endpackage" << stream.endl();
    // end of guard
    if (include_guard) stream << "`endif" << stream.endl();

    return {stream.str(), static_cast<uint32_t>(stream.line_no())};
}

void fix_verilog_ln(Generator* generator, uint32_t offset) {
    // need to fix every variable and statement verilog line number by an offset
    if (!generator->debug) return;
    // fix the variable declaration
    generator->verilog_ln += offset;
    auto const& var_names = generator->get_all_var_names();
    for (auto const& var_name : var_names) {
        auto var = generator->get_var(var_name);
        var->verilog_ln += offset;
    }
    // get all the statement graph
    StatementGraph graph(generator);
    auto stmts = graph.nodes();
    for (auto const& iter : stmts) {
        auto stmt = iter.first;
        stmt->verilog_ln += offset;
    }
}

}  // namespace kratos
