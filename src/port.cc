#include "port.hh"
#include <stdexcept>
#include <unordered_map>
#include "absl/strings/str_format.h"

using absl::StrFormat;
using std::runtime_error;
using std::string;

Port::Port(PortDirection direction, std::string name, uint32_t width, PortType type)
    : direction(direction), type(type), name(std::move(name)), width(width) {
    if ((type == PortType::AsyncReset || type == PortType::Clock || type == PortType::ClockEnable ||
         type == PortType::Reset) &&
        width > 1) {
        throw ::runtime_error(::StrFormat("%s's width has be 1, got %d", name, width));
    }
}

PortSlice Port::operator[](std::tuple<uint32_t, uint32_t> slice) {
    auto const [low, high] = slice;
    if (low > high) {
        throw ::runtime_error(::StrFormat("low (%d) cannot be larger than (%d)", low, high));
    }
    if (high >= width) {
        throw ::runtime_error(
            ::StrFormat("high (%d) has to be smaller than width (%d)", high, width));
    }
    return PortSlice{this, low, high};
}

PortSlice Port::operator[](uint32_t bit) { return (*this)[{bit, bit}]; }

bool operator<(const Port &left, const Port &right) { return left.name < right.name; }

ConstPort::ConstPort(uint64_t value, uint32_t width)
    : Port(PortDirection::In, ::StrFormat("const_%d", value), width, PortType::Const),
      value(value) {}