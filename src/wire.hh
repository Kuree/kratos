#ifndef DUSK_WIRE_HH
#define DUSK_WIRE_HH

#include "port.hh"

struct Wire {
public:
    PortSlice *src = nullptr;
    std::set<PortSlice> sinks;
};

#endif  // DUSK_WIRE_HH
