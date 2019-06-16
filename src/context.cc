#include "context.hh"
#include "expr.hh"
#include "fmt/format.h"
#include "module.hh"

using fmt::format;
using std::runtime_error;
using std::string;
using std::unique_ptr;
using std::vector;

Var &Context::var(const std::string &var_name, uint32_t width) {
    return var(var_name, width, false);
}

Var &Context::var(const std::string &var_name, uint32_t width, bool is_signed) {
    if (vars_.find(var_name) != vars_.end()) {
        Var *v_p = get_var(var_name);
        if (v_p->width != width || v_p->is_signed != is_signed)
            throw std::runtime_error(
                ::format("redefinition of %s with different width/sign", var_name));
        return *v_p;
    }
    vars_.emplace(var_name, std::make_unique<Var>(this, var_name, width, is_signed));
    return *get_var(var_name);
}

void Context::add_expr(const Expr &expr) {
    if (vars_.find(expr.name) == vars_.end()) {
        if (expr.context != this) {
            throw ::runtime_error(::format("%s's context is not the same", expr.name));
        }
        vars_.emplace(expr.name, std::make_unique<Expr>(expr));
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