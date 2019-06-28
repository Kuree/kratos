#include <utility>

#include <filesystem>
#include <fstream>
#include <iostream>
#include <regex>
#include <unordered_set>
#include "fmt/format.h"
#include "generator.hh"
#include "slang/compilation/Compilation.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/text/SourceManager.h"
#include "slang/util/Bag.h"
#include "stmt.hh"

using fmt::format;
using std::runtime_error;
using std::string;
using std::vector;
namespace fs = std::filesystem;

std::map<::string, std::shared_ptr<Port>> get_port_from_verilog(Generator *module,
                                                                const ::string &filename,
                                                                const ::string &module_name) {
    slang::SourceManager source_manager;
    slang::Compilation compilation;
    std::map<::string, std::shared_ptr<Port>> ports;
    auto buffer = source_manager.readSource(filename);
    slang::Bag options;
    auto ast_tree = slang::SyntaxTree::fromBuffer(buffer, source_manager, options);
    compilation.addSyntaxTree(ast_tree);
    const auto &def = compilation.getDefinition(module_name);
    if (!def) {
        throw ::runtime_error(::format("unable to find {0} from {1}", module_name, filename));
    }
    const auto &port_map = def->getPortMap();
    for (auto const &[name, symbol] : port_map) {
        if (symbol->kind == slang::SymbolKind::Port) {
            const auto &p = symbol->as<slang::PortSymbol>();
            // get port direction
            PortDirection direction;
            switch (p.direction) {
                case slang::PortDirection::In:
                    direction = PortDirection::In;
                    break;
                case slang::PortDirection::Out:
                    direction = PortDirection::Out;
                    break;
                case slang::PortDirection::InOut:
                    direction = PortDirection::InOut;
                    break;
                default:
                    throw ::runtime_error("Unknown port direction");
            }
            // get name
            const ::string name = ::string(p.name);
            // get width
            const auto &type = p.getType();
            const auto width = type.getBitWidth();
            const auto is_signed = type.isSigned();
            ports.emplace(name, std::make_shared<Port>(module, direction, name, width,
                                                       PortType::Data, is_signed));
        }
    }

    return ports;
}

Generator Generator::from_verilog(Context *context, const std::string &src_file,
                                  const std::string &top_name,
                                  const std::vector<std::string> &lib_files,
                                  const std::map<std::string, PortType> &port_types) {
    if (!fs::exists(src_file)) throw ::runtime_error(::format("{0} does not exist", src_file));

    Generator mod(context, top_name);
    // the src file will be treated a a lib file as well
    mod.lib_files_.emplace_back(src_file);
    mod.lib_files_ = vector<::string>(lib_files.begin(), lib_files.end());
    // const auto &ports = ;
    const auto ports = get_port_from_verilog(&mod, src_file, top_name);
    for (auto const &[port_name, port] : ports) {
        mod.ports_.emplace(port_name);
        mod.vars_.emplace(port_name, port);
    }
    // verify the existence of each lib files
    for (auto const &filename : mod.lib_files_) {
        if (!fs::exists(filename)) throw ::runtime_error(::format("{0} does not exist", filename));
    }

    // assign port types
    for (auto const &[port_name, port_type] : port_types) {
        if (mod.ports_.find(port_name) == mod.ports_.end())
            throw ::runtime_error(::format("unable to find port {0}", port_name));
        std::shared_ptr<Var> &var_p = mod.vars_.at(port_name);
        std::shared_ptr<Port> port_p = std::static_pointer_cast<Port>(var_p);
        port_p->set_port_type(port_type);
    }

    return mod;
}

Var &Generator::var(const std::string &var_name, uint32_t width) {
    return var(var_name, width, false);
}

Var &Generator::var(const std::string &var_name, uint32_t width, bool is_signed) {
    if (vars_.find(var_name) != vars_.end()) {
        auto v_p = get_var(var_name);
        if (v_p->width != width || v_p->is_signed != is_signed)
            throw std::runtime_error(
                ::format("redefinition of {0} with different width/sign", var_name));
        return *v_p;
    }
    auto p = std::make_shared<Var>(this, var_name, width, is_signed);
    vars_.emplace(var_name, p);
    return *p;
}

std::shared_ptr<Var> Generator::get_var(const std::string &var_name) {
    if (vars_.find(var_name) == vars_.end()) return nullptr;
    return vars_.at(var_name);
}

Port &Generator::port(PortDirection direction, const std::string &port_name, uint32_t width) {
    return port(direction, port_name, width, PortType::Data, false);
}

Port &Generator::port(PortDirection direction, const std::string &port_name, uint32_t width,
                      PortType type, bool is_signed) {
    if (ports_.find(port_name) != ports_.end())
        throw ::runtime_error(::format("{0} already exists in {1}", port_name, name));
    auto p = std::make_shared<Port>(this, direction, port_name, width, type, is_signed);
    vars_.emplace(port_name, p);
    ports_.emplace(port_name);
    return *p;
}

std::shared_ptr<Port> Generator::get_port(const std::string &port_name) {
    if (ports_.find(port_name) == ports_.end()) return nullptr;
    auto var_p = vars_.at(port_name);
    return std::static_pointer_cast<Port>(var_p);
}

Expr &Generator::expr(ExprOp op, const std::shared_ptr<Var> &left,
                      const std::shared_ptr<Var> &right) {
    auto expr = std::make_shared<Expr>(op, left, right);
    if (vars_.find(expr->name) != vars_.end()) {
        auto p = vars_.at(expr->name);
        expr = std::static_pointer_cast<Expr>(p);
    } else {
        vars_.emplace(expr->name, expr);
    }
    return *expr;
}

Const &Generator::constant(int64_t value, uint32_t width) { return constant(value, width, false); }

Const &Generator::constant(int64_t value, uint32_t width, bool is_signed) {
    Const v(this, value, width, is_signed);
    std::shared_ptr<Const> ptr;
    if (vars_.find(v.name) != vars_.end()) {
        ptr = std::static_pointer_cast<Const>(vars_.at(v.name));
    } else {
        ptr = std::make_shared<Const>(this, value, width, is_signed);
        // add a new var
        vars_.emplace(ptr->name, ptr);
    }
    return *ptr;
}

ASTNode *Generator::get_child(uint64_t index) {
    if (index < child_count())
        return stmts_[index].get();
    else
        return nullptr;
}

void Generator::add_child_generator(const std::shared_ptr<Generator> &child, bool merge) {
    children_.emplace(child);
    child->parent_generator_ = this;
    should_child_inline_[child] = merge;
}

void Generator::remove_child_generator(const std::shared_ptr<Generator> &child) {
    if (children_.find(child) != children_.end()) {
        children_.erase(child);
        should_child_inline_.erase(child);
    }
}

std::unordered_set<std::string> Generator::get_vars() {
    std::unordered_set<std::string> result;
    for (auto const &[name, ptr] : vars_) {
        if (ptr->type() != VarType::PortIO) {
            result.emplace(name);
        }
    }
    return result;
}

void Generator::add_stmt(std::shared_ptr<Stmt> stmt) {
    stmt->set_parent(this);
    stmts_.emplace_back(std::move(stmt));
}

std::string Generator::get_unique_variable_name(const std::string &prefix,
                                                const std::string &var_name) {
    // NOTE: this is not thread-safe!
    uint32_t count = 0;
    std::string result_name;
    while (true) {
        if (prefix.empty()) {
            result_name = ::format("{0}_{1}", var_name, count);
        } else {
            result_name = ::format("{0}${1}_{2}", prefix, var_name, count);
        }
        if (!get_var(result_name)) {
            break;
        } else {
            count++;
        }
    }
    return result_name;
}

void Generator::rename_var(const std::string &old_name, const std::string &new_name) {
    auto var = get_var(old_name);
    if (!var) return;
    // Using C++17 to replace the key
    vars_.extract(old_name).key() = new_name;
    // rename the var
    var->name = new_name;
}

void Generator::remove_stmt(const std::shared_ptr<Stmt> &stmt) {
    auto pos = std::find(stmts_.begin(), stmts_.end(), stmt);
    if (pos != stmts_.end()) {
        stmts_.erase(pos);
    }
}

std::shared_ptr<SequentialStmtBlock> Generator::sequential() {
    auto stmt = std::make_shared<SequentialStmtBlock>();
    add_stmt(stmt);
    return stmt;
}

std::shared_ptr<CombinationalStmtBlock> Generator::combinational() {
    auto stmt = std::make_shared<CombinationalStmtBlock>();
    add_stmt(stmt);
    return stmt;
}