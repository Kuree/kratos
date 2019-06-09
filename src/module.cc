#include <regex>
#include <fstream>
#include <iostream>
#include "module.hh"
#include "io.hh"
#include "absl/strings/str_format.h"

using std::vector;
using std::string;
using std::runtime_error;
using absl::StrFormat;

std::vector<Port> get_port_from_verilog(const ::string& src, const ::string &top_name) {
    std::regex re("module[\\w\\W]*?endmodule");    // NOLINT
    std::smatch match;
    if (std::regex_search(src, match, re) && match.size() > 1) {
        // we have at least one match
        for (const auto &match_str: match) {
            std::cout << match_str.str() << std::endl;
        }
    } else {
        throw ::runtime_error(::StrFormat("cannot find module %s", top_name));
    }
    return {};
}

Module Module::from_verilog(const std::string& src_file, const std::string& top_name,
                            const std::vector<std::string> &lib_files) {
    if (!exists(src_file))
        throw ::runtime_error(::StrFormat("%s does not exist", src_file));

    Module mod;
    // the src file will be treated a a lib file as well
    mod.lib_files_.emplace_back(src_file);
    mod.lib_files_ = vector<::string>(lib_files.begin(), lib_files.end());
    std::ifstream src(src_file);
    std::string src_code((std::istreambuf_iterator<char>(src)),
                         std::istreambuf_iterator<char>());
    const auto &ports = get_port_from_verilog(src_code, "test");

    // verify the existence of each lib files
    for (auto const &filename : mod.lib_files_) {
        if (!exists(filename))
            throw ::runtime_error(::StrFormat("%s does not exist", filename));
    }

    return mod;
}