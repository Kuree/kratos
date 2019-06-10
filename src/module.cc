#include <utility>

#include <fstream>
#include <iostream>
#include <regex>
#include <unordered_set>
#include "absl/strings/str_format.h"
#include "absl/strings/str_split.h"
#include "io.hh"
#include "module.hh"

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
                            const std::vector<std::string> &lib_files,
                            const std::map<std::string, PortType> &port_types) {
    if (!exists(src_file)) throw ::runtime_error(::StrFormat("%s does not exist", src_file));

    Module mod(top_name);
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

    // assign port types
    for (auto const &[port_name, port_type] : port_types) {
        if (mod.ports.find(port_name) == mod.ports.end())
            throw ::runtime_error(::StrFormat("unable to find port %s", port_name));
        mod.ports.at(port_name).type = port_type;
    }

    return mod;
}

Var::Var(Module *parent, std::string name, uint32_t width, bool is_signed)
    : name(std::move(name)), width(width), is_signed(is_signed), parent(parent) {}

Var *Module::get_var(const std::string &var_name) {
    if (vars_.find(var_name) == vars_.end()) return nullptr;
    return &vars_.at(var_name);
}

Var &Module::var(const std::string &var_name, uint32_t width, bool is_signed) {
    if (vars_.find(var_name) != vars_.end()) {
        Var *v_p = get_var(var_name);
        if (v_p->width != width || v_p->is_signed != is_signed)
            throw std::runtime_error(
                ::StrFormat("redefinition of %s with different width/sign", var_name));
        return *v_p;
    }
    vars_.emplace(var_name, Var(this, var_name, width, is_signed));
    return *get_var(var_name);
}

void Module::add_var(const Var &var) {
    if (vars_.find(var.name) == vars_.end())
        vars_.emplace(var.name, var);
}

std::pair<Var*, Var*> Var::get_binary_var_ptr(const Var &var) {
    auto left = parent->get_var(name);
    if (left == nullptr)
        throw std::runtime_error(
            ::StrFormat("unable to find port %s from %s", var.name, parent->name));
    auto right = parent->get_var(var.name);
    if (right == nullptr)
        throw std::runtime_error(
            ::StrFormat("unable to find port %s from %s", var.name, parent->name));
    return {left, right};
}

Expr Var::operator-(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return Expr(ExprOp::Minus, left, right);
}

Expr Var::operator-() {
    auto var = parent->get_var(name);
    return Expr(ExprOp::Minus, var, nullptr);
}

Expr Var::operator~() {
    auto var = parent->get_var(name);
    return Expr(ExprOp::UInvert, var, nullptr);
}

Expr Var::operator+() {
    auto var = parent->get_var(name);
    return Expr(ExprOp::UPlus, var, nullptr);
}


Expr Var::operator+(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return Expr(ExprOp::Add, left, right);
}

Expr Var::operator*(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return Expr(ExprOp::Multiply, left, right);
}

Expr Var::operator%(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return Expr(ExprOp::Mod, left, right);
}

Expr Var::operator/(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return Expr(ExprOp::Divide, left, right);
}

Expr Var::operator>>(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return Expr(ExprOp::LogicalShiftRight, left, right);
}

Expr Var::operator<<(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return Expr(ExprOp::ShiftLeft, left, right);
}

Expr Var::ashr(const Var &var) {
    const auto &[left, right] = get_binary_var_ptr(var);
    return Expr(ExprOp::SignedShiftRight, left, right);
}

Expr::Expr(ExprOp op, Var *left, Var *right) : op(op), left(left), right(right) {
    if (left == nullptr) throw std::runtime_error("left operand is null");
    if (right != nullptr && left->parent != right->parent)
        throw std::runtime_error(::StrFormat("%s (%s)'s scope is different from that of %s's (%s)",
                                             left->name, left->parent->name, right->name,
                                             right->parent->name));
    parent = left->parent;
    if (right != nullptr && left->width != right->width)
        throw std::runtime_error(
            ::StrFormat("left (%s) width (%d) doesn't match with right (%s) width (%d", left->name,
                        left->width, right->name, right->width));
    width = left->width;
    if (right != nullptr)
        name = ::StrFormat("%s_%s_%s", left->name, ExprOpStr(op), right->name);
    else
        name = ::StrFormat("%s_%s", ExprOpStr(op), left->name);
    if (right != nullptr)
        is_signed = left->is_signed | right->is_signed;
    else
        is_signed = left->is_signed;

    // add it to parent's vars
    parent->add_var(*this);
}
