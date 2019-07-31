#include "port.hh"
#include <stdexcept>
#include <unordered_map>
#include "except.hh"
#include "fmt/format.h"
#include "generator.hh"
#include "stmt.hh"


using fmt::format;
using std::runtime_error;
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
        throw ::runtime_error(::format("{0}'s width has be 1, got {1}", name, width));
    }
}

void Port::set_port_type(PortType type) { type_ = type; }

PackedStruct::PackedStruct(std::string struct_name,
                           std::vector<std::tuple<std::string, uint32_t, bool>> attributes)
    : struct_name(std::move(struct_name)), attributes(std::move(attributes)) {}

PortPacked::PortPacked(Generator* module, PortDirection direction, const std::string& name,
                       PackedStruct packed_struct_)
    : Port(module, direction, name, 0, 1, PortType::Data, false),
      struct_(std::move(packed_struct_)) {
    // compute the width
    width = 0;
    for (auto const& def : struct_.attributes) {
        width += std::get<1>(def);
    }
}

void PortPacked::set_port_type(PortType) {
    throw ::runtime_error("Cannot set port type for packed struct");
}

PortPackedSlice& PortPacked::operator[](const std::string& member_name) {
    if (members_.find(member_name) != members_.end()) {
        return *members_.at(member_name);
    } else {
        auto ptr = std::make_shared<PortPackedSlice>(this, member_name);
        members_.emplace(member_name, ptr);
        return *ptr;
    }
}

PortPackedSlice::PortPackedSlice(PortPacked* parent, const std::string& member_name)
    : VarSlice(parent, 0, 0), member_name_(member_name) {
    // compute the high and low
    uint32_t low_ = 0;
    bool found = false;
    auto const& struct_ = parent->packed_struct();
    for (auto const& [name, width, is_signed_] : struct_.attributes) {
        if (name == member_name) {
            found = true;
            high = width + low_ - 1;
            low = low_;
            is_signed = is_signed_;
            var_high_ = high;
            var_low_ = low;
            break;
        } else {
            low_ += width;
        }
    }

    if (!found) {
        throw ::runtime_error(
            ::format("{0} does not exist in {1}", member_name, struct_.struct_name));
    }
}

std::string PortPackedSlice::to_string() const {
    return ::format("{0}.{1}", parent_var->to_string(), member_name_);
}

void PortBundleDefinition::add_definition(const std::string& name, uint32_t width, uint32_t size,
                                          bool is_signed, kratos::PortDirection direction,
                                          kratos::PortType type) {
    if (definitions_.find(name) != definitions_.end())
        throw ::runtime_error(name + " already exists");
    definitions_.emplace(name, std::make_tuple(width, size, is_signed, direction, type));
    PortDirection dir;
    if (direction == PortDirection::In) {
        dir = PortDirection::Out;
    } else if (direction == PortDirection::Out) {
        dir = PortDirection::In;
    } else {
        throw ::runtime_error("PortBundle doesn't allow inout");
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
        throw ::runtime_error(::format("Unable to find {0} in port bundle", name));
    auto const& port_name = name_mappings_.at(name);
    return *generator->get_port(port_name);
}

void PortBundleRef::assign(const std::shared_ptr<PortBundleRef>& other, Generator* parent,
                           const std::vector<std::pair<std::string, uint32_t>>& debug_info) {
    // making sure they have the same interface
    auto self_def = definition_->definition();
    auto other_def = other->definition_->definition();
    if (self_def.size() != other_def.size()) {
        throw ::runtime_error("PortBundle definition doesn't match");
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
            for (auto const &entry: debug_info)
                stmt->fn_name_ln.emplace_back(entry);
    }
}

}  // namespace kratos
