#ifndef DUSK_PORT_HH
#define DUSK_PORT_HH

#include <set>
#include <string>
#include <vector>

#include "expr.hh"

enum class PortDirection { In, Out, InOut };

enum class PortType { Data, Clock, AsyncReset, Reset, ClockEnable };

struct Port : public Var {
public:
    PortDirection direction;
    PortType type;

    Port(Module *module, PortDirection direction, const std::string &name, uint32_t width);

    Port(Module *module, PortDirection direction, const std::string &name, uint32_t width,
         PortType type, bool is_signed);
};

#endif  // DUSK_PORT_HH
