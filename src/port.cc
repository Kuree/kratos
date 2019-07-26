#include "port.hh"
#include <stdexcept>
#include <unordered_map>
#include "except.hh"
#include "fmt/format.h"

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

}  // namespace kratos
