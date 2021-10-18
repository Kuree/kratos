#include "interface.hh"

#include "except.hh"
#include "fmt/format.h"

using fmt::format;

namespace kratos {

std::shared_ptr<InterfaceModPortDefinition> InterfaceDefinition::create_modport_def(
    const std::string& name) {
    if (mod_ports_.find(name) != mod_ports_.end())
        throw UserException(::format("{0} already exists in {1}", name, name_));
    auto p = std::make_shared<InterfaceModPortDefinition>(shared_from_this(), name);
    mod_ports_.emplace(name, p);
    return p;
}

std::string InterfaceDefinition::port(const std::string& name, uint32_t width, uint32_t size,
                                      kratos::PortDirection dir) {
    return port(name, width, std::vector<uint32_t>{size}, dir);
}

std::string InterfaceDefinition::port(const std::string& name, uint32_t width,
                                      const std::vector<uint32_t>& size,
                                      enum kratos::PortDirection dir) {
    return port(name, width, size, dir, PortType::Data);
}

std::string InterfaceDefinition::port(const std::string& name, uint32_t width,
                                      const std::vector<uint32_t>& size,
                                      enum kratos::PortDirection dir, PortType type) {
    if (ports_.find(name) != ports_.end())
        throw UserException(::format("{0} already exists in {1}", name, name_));
    ports_.emplace(name, std::make_tuple(width, size, dir, type));
    return name;
}

std::string InterfaceDefinition::input(const std::string& name, uint32_t width, uint32_t size) {
    return port(name, width, size, PortDirection::In);
}

std::string InterfaceDefinition::output(const std::string& name, uint32_t width, uint32_t size) {
    return port(name, width, size, PortDirection::Out);
}

InterfaceDefinition::InterfacePortDef InterfaceDefinition::port(const std::string& name) const {
    if (ports_.find(name) == ports_.end())
        throw UserException(::format("{0} does not exist in {1}", name, name_));
    return ports_.at(name);
}

std::string InterfaceDefinition::var(const std::string& name, uint32_t width, uint32_t size) {
    return var(name, width, std::vector<uint32_t>{size});
}

std::string InterfaceDefinition::var(const std::string& name, uint32_t width,
                                     const std::vector<uint32_t>& size) {
    if (vars_.find(name) != vars_.end())
        throw UserException(::format("{0} already exists in {1}", name, name_));
    vars_.emplace(name, std::make_pair(width, size));
    return name;
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

InterfaceModPortDefinition::InterfaceModPortDefinition(
    std::shared_ptr<kratos::InterfaceDefinition> def, std::string name)
    : def_(std::move(def)), name_(std::move(name)) {}

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
    if (def_->has_port(name)) {
        return def_->port(name);
    } else {
        // create a port def
        auto const& [width, size] = def_->var(name);
        auto port_dir =
            inputs_.find(name) != inputs_.end() ? PortDirection::In : PortDirection::Out;
        return std::make_tuple(width, size, port_dir, PortType::Data);
    }
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

std::string InterfaceModPortDefinition::def_name() const {
    return ::format("{0}.{1}", def_->def_name(), name_);
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

std::string InterfaceRef::base_name() const { return name(); }

std::shared_ptr<InterfaceRef> InterfaceRef::get_modport_ref(const std::string& name) {
    if (mod_ports_.find(name) != mod_ports_.end()) return mod_ports_.at(name);
    auto* definition = dynamic_cast<InterfaceDefinition*>(definition_.get());
    if (definition_->is_modport() || !definition) {
        throw UserException("Cannot create modport from a modport interface");
    }
    auto modports = definition->mod_ports();
    if (modports.find(name) == modports.end())
        throw UserException(
            ::format("Unable to find modport {0} from {1}", name, definition->name()));
    auto modport_def = modports.at(name);
    auto new_ref =
        std::make_shared<InterfaceRef>(modport_def, gen_, ::format("{0}.{1}", name_, name));
    // pass through the variable reference
    // since it's modport, it can only be ports
    auto ports = modport_def->ports();
    for (auto const& port_name : ports) {
        bool is_input = modport_def->inputs().find(name) != modport_def->inputs().end();
        if (has_var(port_name)) {
            // it's a variable
            auto port = std::make_shared<ModportPort>(
                new_ref.get(), &var(port_name), is_input ? PortDirection::In : PortDirection::Out);
            new_ref->modport_ports_.emplace(port_name, port);
            new_ref->port(port_name, port.get());
        } else {
            new_ref->port(port_name, &port(port_name));
        }
    }
    mod_ports_.emplace(name, new_ref);
    new_ref->interface_parent_ = this;
    return new_ref;
}

bool InterfaceRef::has_modport(const std::string& name) {
    auto* definition = dynamic_cast<InterfaceDefinition*>(definition_.get());
    if (definition_->is_modport() || !definition) {
        return false;
    }
    auto modports = definition->mod_ports();
    return modports.find(name) != modports.end();
}

}  // namespace kratos
