#include "interface.hh"

#include "except.hh"
#include "fmt/format.h"

using fmt::format;

namespace kratos {

std::shared_ptr<InterfaceModPortDefinition> InterfaceDefinition::create_modport_def(
    const std::string& name) {
    if (mod_ports_.find(name) != mod_ports_.end())
        throw UserException(::format("{0} already exists in {1}", name, name_));
    auto p = std::make_shared<InterfaceModPortDefinition>(this, name);
    mod_ports_.emplace(name, p);
    return p;
}

void InterfaceDefinition::port(const std::string& name, uint32_t width, uint32_t size,
                               kratos::PortDirection dir) {
    port(name, width, std::vector<uint32_t>{size}, dir);
}

void InterfaceDefinition::port(const std::string& name, uint32_t width,
                               const std::vector<uint32_t>& size, enum kratos::PortDirection dir) {
    if (ports_.find(name) != ports_.end())
        throw UserException(::format("{0} already exists in {1}", name, name_));
    ports_.emplace(name, std::make_tuple(width, size, dir));
}

void InterfaceDefinition::input(const std::string& name, uint32_t width, uint32_t size) {
    port(name, width, size, PortDirection::In);
}

void InterfaceDefinition::output(const std::string& name, uint32_t width, uint32_t size) {
    port(name, width, size, PortDirection::Out);
}

InterfaceDefinition::InterfacePortDef InterfaceDefinition::port(const std::string& name) const {
    if (ports_.find(name) == ports_.end())
        throw UserException(::format("{0} does not exist in {1}", name, name_));
    return ports_.at(name);
}

void InterfaceDefinition::var(const std::string& name, uint32_t width, uint32_t size) {
    var(name, width, std::vector<uint32_t>{size});
}

void InterfaceDefinition::var(const std::string& name, uint32_t width,
                              const std::vector<uint32_t>& size) {
    if (vars_.find(name) != vars_.end())
        throw UserException(::format("{0} already exists in {1}", name, name_));
    vars_.emplace(name, std::make_pair(width, size));
}

std::set<std::string> InterfaceDefinition::ports() const {
    std::set<std::string> result;
    for (auto const& iter : ports_) result.emplace(iter.first);
    return result;
}

std::set<std::string> InterfaceDefinition::vars() const {
    std::set<std::string> result;
    for (auto const& iter : vars_) result.emplace(iter.first);
    return result;
}

InterfaceDefinition::InterfaceVarDef InterfaceDefinition::var(const std::string& name) const {
    if (vars_.find(name) == vars_.end())
        throw UserException(::format("{0} does not exist in {1}", name, name_));
    return vars_.at(name);
}

bool InterfaceDefinition::has_port(const std::string& name) const {
    return ports_.find(name) != ports_.end();
}

bool InterfaceDefinition::has_var(const std::string& name) const {
    return vars_.find(name) != vars_.end();
}

InterfaceModPortDefinition::InterfaceModPortDefinition(kratos::InterfaceDefinition* def,
                                                       std::string name)
    : def_(def), name_(std::move(name)) {}

void InterfaceModPortDefinition::set_output(const std::string& name) {
    if (def_->has_port(name)) {
        // this is a port
        auto const& port_def = def_->port(name);
        auto dir = std::get<2>(port_def);
        if (dir != PortDirection::Out) {
            throw UserException(::format(
                "{0} is not declared as an output but is used as one in {1}", name, name_));
        }
        outputs_.emplace(name);
    } else if (def_->has_var(name)) {
        // this is a variable
        outputs_.emplace(name);
    }
}

IDefinition::InterfacePortDef InterfaceModPortDefinition::port(const std::string& name) const {
    if (!has_port(name)) throw UserException(::format("{0} does not exist", name));
    return def_->port(name);
}

IDefinition::InterfaceVarDef InterfaceModPortDefinition::var(const std::string&) const {
    throw UserException(::format("{0} as modport does not have internal variables", name_));
}

std::set<std::string> InterfaceModPortDefinition::ports() const {
    std::set<std::string> result;
    for (auto const& name : inputs_) result.emplace(name);
    for (auto const& name : outputs_) result.emplace(name);
    return result;
}

std::set<std::string> InterfaceModPortDefinition::vars() const { return {}; }

void InterfaceModPortDefinition::set_input(const std::string& name) {
    if (def_->has_port(name)) {
        // this is a port
        auto const& port_def = def_->port(name);
        auto dir = std::get<2>(port_def);
        if (dir != PortDirection::In) {
            throw UserException(
                ::format("{0} is not declared as an input but is used as one in {1}", name, name_));
        }
        inputs_.emplace(name);
    } else if (def_->has_var(name)) {
        // this is a variable
        inputs_.emplace(name);
    }
}

Var& InterfaceRef::var(const std::string& name) const {
    if (!has_var(name)) {
        throw UserException(::format("{0} not found in {1}", name, name_));
    }
    return *vars_.at(name);
}

Port& InterfaceRef::port(const std::string& name) const {
    if (!has_port(name)) {
        throw UserException(::format("{0} not found in {1}", name, name_));
    }
    return *ports_.at(name);
}

}  // namespace kratos
