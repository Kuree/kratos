#ifndef DUSK_WIRE_HH
#define DUSK_WIRE_HH

#include "port.hh"

struct Wire {
public:
    VarSlice *src = nullptr;
    std::set<VarSlice> sinks;
};

#endif  // DUSK_WIRE_HH
