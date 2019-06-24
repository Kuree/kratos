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
    auto const &p = std::make_shared<Generator>(this, name);
    modules_[name].emplace(p);
    return *p;
}

void Context::remove(Generator *generator) {
    if (modules_.find(generator->name) == modules_.end())
        return;
    auto &module_set = modules_.at(generator->name);
    // TODO:
    //  Write a complete pass to remove the generator
    //  1. remove any connections/assignments
    //  2. remove itself from the parent
    auto const &shared_ptr = generator->shared_from_this();
    if (module_set.find(shared_ptr) != module_set.end())
        module_set.erase(shared_ptr);
}