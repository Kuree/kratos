#ifndef DUSK_MODULE_HH
#define DUSK_MODULE_HH
#include <string>
#include <vector>

#include "port.hh"

class Module {
public:
    std::string name;
    std::set<Port> ports;

    static Module from_verilog(const std::string &src_file, const std::string &top_name,
        const std::vector<std::string> &lib_files);
private:
    std::vector<std::string> lib_files_;
};



#endif //DUSK_MODULE_HH
