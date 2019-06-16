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

std::map<::string, Port> get_port_from_verilog(Context *context, const ::string &filename,
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
            ports.emplace(name, Port(context, direction, name, width, PortType::Data, is_signed));
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
    mod.ports = get_port_from_verilog(context, src_file, top_name);
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
