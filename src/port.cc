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

void Port::set_port_type(PortType type) { type_ = type; }

void Port::set_active_high(bool value) {
    if (width() != 1)
        throw VarException(
            ::format("{0}'s width is not 1, which can not be set as active high/low", name),
            {this});
    active_high_ = value;
}

PortPacked::PortPacked(Generator* module, PortDirection direction, const std::string& name,
                       PackedStruct packed_struct_)
    : Port(module, direction, name, 0, 1, PortType::Data, false),
      struct_(std::move(packed_struct_)) {
    // compute the width
    uint32_t width = 0;
    for (auto const& def : struct_.attributes) {
        width += std::get<1>(def);
    }
    var_width_ = width;
}

void PortPacked::set_port_type(PortType) {
    throw UserException("Cannot set port type for packed struct");
}

PackedSlice& PortPacked::operator[](const std::string& member_name) {
    auto ptr = std::make_shared<PackedSlice>(this, member_name);
    slices_.emplace(ptr);
    return *ptr;
}

std::set<std::string> PortPacked::member_names() const {
    std::set<std::string> result;
    for (auto& def : struct_.attributes) {
        result.emplace(std::get<0>(def));
    }
    return result;
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

std::shared_ptr<PortBundleDefinition> PortBundleDefinition::flip() {
    if (flipped_) return flipped_;
    flipped_ = std::make_shared<PortBundleDefinition>(name_);
    flipped_->definitions_ = flipped_definitions_;
    flipped_->flipped_definitions_ = definitions_;
    flipped_->debug_info_ = debug_info_;
    flipped_->flipped_ = shared_from_this();
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
    auto self_def = definition_->definition();
    auto other_def = other->definition_->definition();
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

}  // namespace kratos
