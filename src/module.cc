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

void visit_module_def(const slang::SyntaxNode *node, const ::string &module_name,
                      slang::PortListSyntax **list) {
    if (*list)
        // we're done
        return;
    uint32_t count = node->getChildCount();
    for (uint32_t i = 0; i < count; i++) {
        auto const &child = node->childNode(i);
        if (!child) continue;
        if (child->kind == slang::SyntaxKind::ModuleHeader) {
            auto const &header = child->as<slang::ModuleHeaderSyntax>();
            if (header.name.valueText() == module_name) {
                *list = header.ports;
            }
        } else {
            visit_module_def(child, module_name, list);
        }
    }
}

std::map<::string, Port> get_port_from_verilog(const ::string &filename,
                                               const ::string &module_name) {
    slang::SourceManager source_manager;
    auto buffer = source_manager.readSource(filename);
    slang::Bag options;
    auto ast_tree = slang::SyntaxTree::fromBuffer(buffer, source_manager, options);
    const auto &root = ast_tree->root();
    slang::PortListSyntax *port_list_syntax = nullptr;
    visit_module_def(&root, module_name, &port_list_syntax);
    if (!port_list_syntax) {
        throw ::runtime_error(
            ::format("unable to find module %s from file %s", module_name, filename));
    }
    std::map<::string, Port> ports;
    if (port_list_syntax->kind == slang::SyntaxKind::AnsiPortList) {
        auto const &port_list = port_list_syntax->as<slang::AnsiPortListSyntax>();
        for (auto const &member : port_list.ports) {
            std::cout << member->attributes.size() << std::endl;
        }
    } else if (port_list_syntax->kind == slang::SyntaxKind::NonAnsiPortList) {
        auto const &port_list = port_list_syntax->as<slang::NonAnsiPortListSyntax>();
        for (auto const &member : port_list.ports) {
            if (member->kind == slang::SyntaxKind::ImplicitNonAnsiPort) {
                auto const &p = member->as<slang::ImplicitNonAnsiPortSyntax>();
                ::string port_name =
                    ::string(p.expr->as<slang::PortReferenceSyntax>().name.valueText());
                Port port(PortDirection::Undefined, port_name, 1);
                ports.emplace(port_name, port);
            } else {
                auto const &p = member->as<slang::ExplicitNonAnsiPortSyntax>();
                ::string port_name = p.expr->toString();
                std::cout << port_name << std::endl;
                throw ::runtime_error("not implemented");
            }
        }
    }
    // if we have any undefined port direction, we need to loop through the ast mody
    // to figure out the direction, i.e. implicit port
    std::unordered_set<::string> implicit_ports;
    for (auto const &[name, port]: ports) {
        if (port.direction == PortDirection::Undefined) {
            implicit_ports.emplace(name);
        }
    }
    if (!implicit_ports.empty()) {
        
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
    mod.ports = get_port_from_verilog(src_file, top_name);
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
