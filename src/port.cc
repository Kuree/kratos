#include "port.hh"
#include <stdexcept>
#include <unordered_map>
#include "fmt/format.h"

using fmt::format;
using std::runtime_error;
using std::string;

Port::Port(Context* c, PortDirection direction, const std::string& name, uint32_t width)
    : Port(c, direction, name, width, PortType::Data, false) {}

Port::Port(Context* c, PortDirection direction, const ::string& name, uint32_t width, PortType type,
           bool is_signed)
    : Var(c, name, width, is_signed), direction(direction), type(type) {
    if ((type == PortType::AsyncReset || type == PortType::Clock || type == PortType::ClockEnable ||
         type == PortType::Reset) &&
        width > 1) {
        throw ::runtime_error(::format("%s's width has be 1, got %d", name, width));
    }
}
