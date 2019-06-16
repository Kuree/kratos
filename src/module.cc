#include <utility>

#include <fstream>
#include <iostream>
#include <regex>
#include <unordered_set>
#include "fmt/format.h"
#include "io.hh"
#include "module.hh"
#include "slang/compilation/Compilation.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/text/SourceManager.h"
#include "slang/util/Bag.h"

using fmt::format;
using std::runtime_error;
using std::string;
using std::vector;

std::map<::string, Port> get_port_from_verilog(Module *module, const ::string &filename,
                                               const ::string &module_name) {
    slang::SourceManager source_manager;
    slang::Compilation compilation;
    std::map<::string, Port> ports;
    auto buffer = source_manager.readSource(filename);
    slang::Bag options;
    auto ast_tree = slang::SyntaxTree::fromBuffer(buffer, source_manager, options);
    compilation.addSyntaxTree(ast_tree);
    const auto &def = compilation.getDefinition(module_name);
    if (!def) {
        throw ::runtime_error(::format("unable to find %s from %s", module_name, filename));
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
            ports.emplace(name, Port(module, direction, name, width, PortType::Data, is_signed));
        }
    }

    return ports;
}

Module Module::from_verilog(Context *context, const std::string &src_file,
                            const std::string &top_name, const std::vector<std::string> &lib_files,
                            const std::map<std::string, PortType> &port_types) {
    if (!exists(src_file)) throw ::runtime_error(::format("%s does not exist", src_file));

    Module mod(context, top_name);
    // the src file will be treated a a lib file as well
    mod.lib_files_.emplace_back(src_file);
    mod.lib_files_ = vector<::string>(lib_files.begin(), lib_files.end());
    // const auto &ports = ;
    mod.ports = get_port_from_verilog(&mod, src_file, top_name);
    // verify the existence of each lib files
    for (auto const &filename : mod.lib_files_) {
        if (!exists(filename)) throw ::runtime_error(::format("%s does not exist", filename));
    }

    // assign port types
    for (auto const &[port_name, port_type] : port_types) {
        if (mod.ports.find(port_name) == mod.ports.end())
            throw ::runtime_error(::format("unable to find port %s", port_name));
        mod.ports.at(port_name).type = port_type;
    }

    return mod;
}


Var &Module::var(const std::string &var_name, uint32_t width) {
    return var(var_name, width, false);
}

Var &Module::var(const std::string &var_name, uint32_t width, bool is_signed) {
    if (vars_.find(var_name) != vars_.end()) {
        Var *v_p = get_var(var_name);
        if (v_p->width != width || v_p->is_signed != is_signed)
            throw std::runtime_error(
                ::format("redefinition of %s with different width/sign", var_name));
        return *v_p;
    }
    vars_.emplace(var_name, Var(this, var_name, width, is_signed));
    return *get_var(var_name);
}

void Module::add_expr(const Expr &expr) {
    if (vars_.find(expr.name) == vars_.end()) {
        if (expr.module != this) {
            throw ::runtime_error(::format("%s's context is not the same", expr.name));
        }
        vars_.emplace(expr.name, expr);
    }
}

Var *Module::get_var(const std::string &var_name) {
    if (vars_.find(var_name) == vars_.end()) return nullptr;
    return &vars_.at(var_name);
}