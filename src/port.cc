#include "port.hh"
#include <stdexcept>
#include <unordered_map>
#include "fmt/format.h"

using fmt::format;
using std::runtime_error;
using std::string;

Port::Port(Generator* module, PortDirection direction, const ::string& name, uint32_t width,
           PortType type, bool is_signed)
    : Var(module, name, width, is_signed, VarType::PortIO), direction_(direction), type_(type) {
    if ((type == PortType::AsyncReset || type == PortType::Clock || type == PortType::ClockEnable ||
         type == PortType::Reset) &&
        width > 1) {
        throw ::runtime_error(::format("{0}'s width has be 1, got {1}", name, width));
    }
}

void Port::set_port_type(PortType type) {
    type_ = type;
}
