#include "context.hh"
#include "expr.hh"
#include "fmt/format.h"
#include "module.hh"

using fmt::format;
using std::runtime_error;
using std::string;
using std::unique_ptr;
using std::vector;


Module &Context::module(const std::string &name) {
    ::vector<::unique_ptr<Module>> &module_set = modules_[name];
    module_set.emplace_back(std::make_unique<Module>(this, name));
    return *(module_set.back());
}