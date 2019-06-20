#include "context.hh"
#include "expr.hh"
#include "fmt/format.h"
#include "generator.hh"

using fmt::format;
using std::runtime_error;
using std::string;
using std::unique_ptr;
using std::vector;

Generator &Context::generator(const std::string &name) {
    ::vector<::unique_ptr<Generator>> &module_set = modules_[name];
    module_set.emplace_back(std::make_unique<Generator>(this, name));
    return *(module_set.back());
}