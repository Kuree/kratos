#include "context.hh"
#include "absl/strings/str_format.h"
#include "absl/strings/str_split.h"
#include "expr.hh"
#include "module.hh"

using absl::StrFormat;
using std::runtime_error;
using std::string;
using std::unique_ptr;
using std::vector;

Var& Context::var(const std::string &var_name, uint32_t width) {
    return var(var_name, width, false);
}

Var& Context::var(const std::string &var_name, uint32_t width, bool is_signed) {
    if (vars_.find(var_name) != vars_.end()) {
        Var *v_p = get_var(var_name);
        if (v_p->width != width || v_p->is_signed != is_signed)
            throw std::runtime_error(
                ::StrFormat("redefinition of %s with different width/sign", var_name));
        return *v_p;
    }
    vars_.emplace(var_name, std::make_unique<Var>(this, var_name, width, is_signed));
    return *get_var(var_name);
}

void Context::add_var(const Var &var) {
    if (vars_.find(var.name) == vars_.end()) {
        if (var.context != this) {
            throw ::runtime_error(::StrFormat("%s's context is not the same", var.name));
        }
        vars_.emplace(var.name, std::make_unique<Var>(var));
    }
}

Var *Context::get_var(const std::string &var_name) {
    if (vars_.find(var_name) == vars_.end()) return nullptr;
    return vars_.at(var_name).get();
}

Module &Context::module(const std::string &name) {
    ::vector<::unique_ptr<Module>> &module_set = modules_[name];
    module_set.emplace_back(std::make_unique<Module>(this, name));
    return *(module_set.back());
}