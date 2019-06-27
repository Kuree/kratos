#ifndef KRATOS_PORT_HH
#define KRATOS_PORT_HH

#include <set>
#include <string>
#include <vector>

#include "expr.hh"

enum class PortDirection { In, Out, InOut };

enum class PortType { Data, Clock, AsyncReset, Reset, ClockEnable };

struct Port : public Var {
public:
    Port(Generator *module, PortDirection direction, const std::string &name, uint32_t width,
         PortType type, bool is_signed);

    PortDirection port_direction() const { return direction_; }
    PortType port_type() const { return type_; }

    void set_port_type(PortType type);

private:
    PortDirection direction_;
    PortType type_;
};

#endif  // KRATOS_PORT_HH
