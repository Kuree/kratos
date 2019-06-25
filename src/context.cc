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
    if (modules_.find(generator->name) == modules_.end()) return;
    auto &module_set = modules_.at(generator->name);
    // TODO:
    //  Write a complete pass to remove the generator
    //  1. remove any connections/assignments
    //  2. remove itself from the parent
    auto const &shared_ptr = generator->shared_from_this();
    if (module_set.find(shared_ptr) != module_set.end()) module_set.erase(shared_ptr);
}

void Context::add_hash(Generator *generator, uint64_t hash) {
    if (generator_hash_.find(generator) != generator_hash_.end())
        throw ::runtime_error(::format("{0}'s hash has already been computed", generator->name));
    generator_hash_[generator] = hash;
}

bool Context::has_hash(Generator *generator) {
    return generator_hash_.find(generator) != generator_hash_.end();
}

uint64_t Context::get_hash(Generator *generator) {
    if (!has_hash(generator))
        throw ::runtime_error(::format("{0}'s hash has not been computed", generator->name));
    return generator_hash_.at(generator);
}