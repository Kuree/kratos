#include "module.hh"
#include <fstream>
#include <iostream>
#include <regex>
#include <unordered_set>
#include "absl/strings/str_format.h"
#include "absl/strings/str_split.h"
#include "io.hh"

using absl::StrFormat;
using std::runtime_error;
using std::string;
using std::vector;

std::map<::string, Port> get_port_from_mod_def(const ::string &mod_def) {
    std::map<::string, Port> result;
    std::unordered_set<::string> ignore_list = {"logic", "reg", "wire"};
    std::regex re("(input|output)\\s?([\\w,\\s_$\\[\\]:])+", std::regex::ECMAScript);  // NOLINT
    std::smatch match;
    ::string::const_iterator iter = mod_def.cbegin();
    while (std::regex_search(iter, mod_def.end(), match, re)) {
        if (match.size() > 1) {
            ::string port_declaration = ::string(match[0].first, match[0].second);
            ::vector<::string> const tokens =
                absl::StrSplit(port_declaration, absl::ByAnyChar(", "));
            // the first one has to be either input or output
            if (tokens.size() < 2)
                throw ::runtime_error(::StrFormat("unable to parse %s", port_declaration));
            ::string input_type = tokens[0];
            PortDirection direction;
            if (input_type == "input")
                direction = PortDirection::In;
            else if (input_type == "output")
                direction = PortDirection::Out;
            else
                throw ::runtime_error(
                    ::StrFormat("%s has to be either input or output", input_type));
            // determine the reset
            uint32_t i = 1;
            uint32_t high = 0;
            uint32_t low = 0;
            while (i < tokens.size()) {
                auto token = tokens[i];
                if (token.empty()) {
                    i++;
                    continue;
                }
                if (token[0] == '[' && token[token.size() - 1] != ']') {
                    token.append(tokens[++i]);
                }
                if (token[0] == '[' && token[token.size() - 1] == ']') {
                    // determine the size
                    ::vector<::string> size_tokens =
                        absl::StrSplit(token, absl::ByAnyChar("[:] "), absl::SkipEmpty());
                    if (size_tokens.size() != 2)
                        throw ::runtime_error(::StrFormat("unable to parse %s", token));
                    high = std::stoi(size_tokens[0]);
                    low = std::stoi(size_tokens[1]);
                    if (high < low)
                        throw ::runtime_error(
                            ::StrFormat("only [hi:lo] is supported, got [%d:%d]", high, low));
                } else {
                    if (token[0] == '[')
                        throw ::runtime_error(::StrFormat("unable to parse %s", port_declaration));
                    const auto &port_name = token;
                    uint32_t width = high - low + 1;
                    Port p(direction, port_name, width);
                    result.emplace(port_name, p);
                }

                i++;
            }
        }
        iter = match[0].second;
    }
    return result;
}

std::map<::string, Port> get_port_from_verilog(const ::string &src, const ::string &top_name) {
    std::regex re("module\\s+([\\w_$]+)[\\w\\W]*?endmodule", std::regex::ECMAScript);  // NOLINT
    std::smatch match;
    ::string::const_iterator iter = src.cbegin();
    ::string module_def;
    while (std::regex_search(iter, src.end(), match, re)) {
        if (match.size() > 1) {
            ::string module_name = ::string(match[1].first, match[1].second);
            if (module_name == top_name) {
                module_def = ::string(match[0].first, match[0].second);
                break;
            }
        }
        iter = match[0].second;
    }
    if (module_def.empty())
        throw ::runtime_error(::StrFormat("Unable to find %s definition", top_name));
    return get_port_from_mod_def(module_def);
}

Module Module::from_verilog(const std::string &src_file, const std::string &top_name,
                            const std::vector<std::string> &lib_files) {
    if (!exists(src_file)) throw ::runtime_error(::StrFormat("%s does not exist", src_file));

    Module mod;
    // the src file will be treated a a lib file as well
    mod.lib_files_.emplace_back(src_file);
    mod.lib_files_ = vector<::string>(lib_files.begin(), lib_files.end());
    std::ifstream src(src_file);
    std::string src_code((std::istreambuf_iterator<char>(src)), std::istreambuf_iterator<char>());
    const auto &ports = get_port_from_verilog(src_code, top_name);
    mod.ports = ports;
    // verify the existence of each lib files
    for (auto const &filename : mod.lib_files_) {
        if (!exists(filename)) throw ::runtime_error(::StrFormat("%s does not exist", filename));
    }

    return mod;
}