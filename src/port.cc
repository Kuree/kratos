#include "port.hh"
#include <stdexcept>
#include <unordered_map>
#include "except.hh"
#include "fmt/format.h"
#include "generator.hh"
#include "stmt.hh"

using fmt::format;
using std::string;

namespace kratos {

Port::Port(Generator* module, PortDirection direction, const ::string& name, uint32_t width,
           uint32_t size, PortType type, bool is_signed)
    : Var(module, name, width, size, is_signed, VarType::PortIO),
      direction_(direction),
      type_(type) {
    if ((type == PortType::AsyncReset || type == PortType::Clock || type == PortType::ClockEnable ||
         type == PortType::Reset) &&
        width > 1) {
        throw UserException(::format("{0}'s width has be 1, got {1}", name, width));
    }
}

Port::Port(kratos::Generator* module, kratos::PortDirection direction, const std::string& name,
           uint32_t width, const std::vector<uint32_t>& size, kratos::PortType type, bool is_signed)
    : Var(module, name, width, size, is_signed, VarType::PortIO),
      direction_(direction),
      type_(type) {
    if ((type == PortType::AsyncReset || type == PortType::Clock || type == PortType::ClockEnable ||
         type == PortType::Reset) &&
        width > 1) {
        throw UserException(::format("{0}'s width has be 1, got {1}", name, width));
    }
}

void Port::set_port_type(PortType type) { type_ = type; }

void Port::set_active_high(bool value) {
    if (width() != 1)
        throw VarException(
            ::format("{0}'s width is not 1, which can not be set as active high/low", name),
            {this});
    active_high_ = value;
}

EnumPort::EnumPort(kratos::Generator* m, kratos::PortDirection direction, const std::string& name,
                   const std::shared_ptr<Enum>& enum_type)
    : Port(m, direction, name, enum_type->width(), 1, PortType::Data, false),
      enum_type_(enum_type.get()) {}

std::shared_ptr<AssignStmt> EnumPort::assign(const std::shared_ptr<Var>& var, AssignmentType type) {
    // TODO: refactor this
    if (!var->is_enum())
        throw VarException("Cannot assign enum type to non enum type", {this, var.get()});
    if (var->type() == VarType::ConstValue) {
        auto p = var->as<EnumConst>();
        if (p->enum_def()->name != enum_type_->name)
            throw VarException("Cannot assign different enum type", {this, var.get()});
    } else {
        auto p = dynamic_cast<EnumType*>(var.get());
        if (!p) throw InternalException("Unable to obtain enum definition");
        if (p->enum_type()->name != enum_type_->name) {
            throw VarException("Cannot assign different enum type", {this, var.get()});
        }
    }
    return Var::assign(var, type);
}

PortPackedStruct::PortPackedStruct(Generator* module, PortDirection direction,
                                   const std::string& name, PackedStruct packed_struct_)
    : Port(module, direction, name, 0, 1, PortType::Data, false),
      struct_(std::move(packed_struct_)) {
    // compute the width
    uint32_t width = 0;
    for (auto const& def : struct_.attributes) {
        width += std::get<1>(def);
    }
    var_width_ = width;
}

void PortPackedStruct::set_port_type(PortType) {
    throw UserException("Cannot set port type for packed struct");
}

PackedSlice& PortPackedStruct::operator[](const std::string& member_name) {
    auto ptr = std::make_shared<PackedSlice>(this, member_name);
    slices_.emplace(ptr);
    return *ptr;
}

std::set<std::string> PortPackedStruct::member_names() const {
    std::set<std::string> result;
    for (auto& def : struct_.attributes) {
        result.emplace(std::get<0>(def));
    }
    return result;
}

void PortPackedStruct::set_is_packed(bool value) {
    if (!value) throw UserException("Unable to set packed struct unpacked");
}

void PortBundleDefinition::add_definition(const std::string& name, uint32_t width, uint32_t size,
                                          bool is_signed, kratos::PortDirection direction,
                                          kratos::PortType type) {
    if (definitions_.find(name) != definitions_.end())
        throw UserException(name + " already exists");
    definitions_.emplace(name, std::make_tuple(width, size, is_signed, direction, type));
    PortDirection dir;
    if (direction == PortDirection::In) {
        dir = PortDirection::Out;
    } else if (direction == PortDirection::Out) {
        dir = PortDirection::In;
    } else {
        throw UserException("PortBundle doesn't allow inout");
    }
    flipped_definitions_.emplace(name, std::make_tuple(width, size, is_signed, dir, type));
}

PortBundleDefinition PortBundleDefinition::flip() {
    PortBundleDefinition flipped_;
    flipped_.definitions_ = flipped_definitions_;
    flipped_.flipped_definitions_ = definitions_;
    flipped_.debug_info_ = debug_info_;
    return flipped_;
}

Port& PortBundleRef::get_port(const std::string& name) {
    if (name_mappings_.find(name) == name_mappings_.end())
        throw UserException(::format("Unable to find {0} in port bundle", name));
    auto const& port_name = name_mappings_.at(name);
    return *generator->get_port(port_name);
}

void PortBundleRef::assign(const std::shared_ptr<PortBundleRef>& other, Generator* parent,
                           const std::vector<std::pair<std::string, uint32_t>>& debug_info) {
    // making sure they have the same interface
    auto self_def = definition_.definition();
    auto other_def = other->definition_.definition();
    if (self_def.size() != other_def.size()) {
        throw UserException("PortBundle definition doesn't match");
    }
    for (auto const& iter : self_def) {
        auto attr_name = iter.first;
        auto self_real_port = name_mappings_.at(attr_name);
        auto self_port = generator->get_port(self_real_port);
        if (other_def.find(attr_name) == other_def.end())
            throw VarException(
                ::format("Unable to find {0} from {1}", attr_name, other->generator->name),
                {self_port.get()});
        auto other_real_port = other->name_mappings_.at(attr_name);
        auto other_port = other->generator->get_port(other_real_port);
        // make stmt
        auto stmt = parent->wire_ports(self_port, other_port);
        if (parent->debug)
            for (auto const& entry : debug_info) stmt->fn_name_ln.emplace_back(entry);
    }
}

std::set<std::string> PortBundleRef::member_names() const {
    std::set<std::string> result;
    for (auto const& def : name_mappings_) result.emplace(def.first);
    return result;
}

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
    if (vars_.find(name) != vars_.end())
        throw UserException(::format("{0} already exists in {1}", name, name_));
    vars_.emplace(name, std::make_pair(width, size));
}

std::pair<uint32_t, uint32_t> InterfaceDefinition::var(const std::string& name) const {
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

void InterfaceVarMapping::set_var(const std::string& name, kratos::Var* var) {
    gen_vars_.emplace(name, var);
}

Var* InterfaceVarMapping::get_var(const std::string& name) const {
    if (gen_vars_.find(name) != gen_vars_.end())
        return gen_vars_.at(name);
    else
        return nullptr;
}

InterfaceModPortDefinition::InterfaceModPortDefinition(kratos::InterfaceDefinition* def,
                                                       std::string name)
    : def_(def), name_(std::move(name)) {}

void InterfaceModPortDefinition::output(const std::string& name) {
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

void InterfaceModPortDefinition::input(const std::string& name) {
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

std::string InterfaceModPortDefinition::to_string() const {
    return ::format("{0}.{1}", def_->to_string(), name_);
}

}  // namespace kratos
