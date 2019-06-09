#ifndef DUSK_MODULE_HH
#define DUSK_MODULE_HH
#include <string>

#include "port.hh"

class Module {
public:
    std::string name;
    std::set<Port> ports;
};



#endif //DUSK_MODULE_HH
