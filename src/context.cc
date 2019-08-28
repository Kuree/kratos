#include "context.hh"
#include "except.hh"
#include "fmt/format.h"
#include "generator.hh"

using fmt::format;
using std::runtime_error;
using std::string;

namespace kratos {

Generator &Context::generator(const std::string &name) {
    auto const &p = std::make_shared<Generator>(this, name);
    modules_[name].emplace(p);
    return *p;
}

Generator Context::empty_generator() { return Generator(this, ""); }

void Context::add(Generator *generator) {
    modules_[generator->name].emplace(generator->shared_from_this());
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

void Context::add_hash(const Generator *generator, uint64_t hash) {
    if (generator_hash_.find(generator) != generator_hash_.end())
        throw InternalException(::format("{0}'s hash has already been computed", generator->name));
    generator_hash_[generator] = hash;
}

bool Context::has_hash(const Generator *generator) const {
    return generator_hash_.find(generator) != generator_hash_.end();
}

uint64_t Context::get_hash(const Generator *generator) const {
    if (!has_hash(generator))
        throw ::runtime_error(::format("{0}'s hash has not been computed", generator->name));
    return generator_hash_.at(generator);
}

void Context::change_generator_name(Generator *generator, const std::string &new_name) {
    if (new_name.empty() || generator->name.empty()) {
        // don't care names
        generator->name = new_name;
        return;
    }
    // first we need to make sure that the generator is within the context
    auto const &old_name = generator->name;
    if (generator->context() != this)
        throw UserException(::format("{0}'s context is different", old_name));
    // remove it from the list
    auto shared_ptr = generator->shared_from_this();
    if (modules_.find(generator->name) == modules_.end())
        throw UserException(::format("cannot find generator {0} in context", old_name));
    auto &list = modules_.at(generator->name);
    auto pos = std::find(list.begin(), list.end(), shared_ptr);
    if (pos == list.end())
        throw UserException(::format("unable to find generator {0} in context", old_name));
    // we need to erase it
    list.erase(pos);
    // change it's name and put it to a new list
    generator->name = new_name;
    modules_[new_name].emplace(shared_ptr);
    // change the cloned names as well
    for (auto &g : generator->get_clones()) {
        g->name = new_name;
    }
}

bool Context::generator_name_exists(const std::string &name) const {
    return modules_.find(name) != modules_.end();
}

std::set<std::shared_ptr<Generator>> Context::get_generators_by_name(
    const std::string &name) const {
    if (!generator_name_exists(name)) return {};
    return modules_.at(name);
}

std::unordered_set<std::string> Context::get_generator_names() const {
    std::unordered_set<std::string> result;
    for (auto const &iter : modules_) {
        result.emplace(iter.first);
    }
    return result;
}

void Context::clear() {
    modules_.clear();
    clear_hash();
}

}  // namespace kratos
