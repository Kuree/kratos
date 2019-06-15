#include <utility>

#ifndef DUSK_MODULE_HH
#define DUSK_MODULE_HH
#include <map>
#include <string>
#include <unordered_map>
#include <vector>

#include "context.hh"
#include "port.hh"

class Module {
public:
    std::string name;
    std::map<std::string, Port> ports;

    static Module from_verilog(Context *context, const std::string &src_file,
                               const std::string &top_name,
                               const std::vector<std::string> &lib_files,
                               const std::map<std::string, PortType> &port_types);

    Module(Context *context, std::string name) : name(std::move(name)), context(context) {}

    void add_port(const Port &port) { ports.emplace(port.name, port); }

private:
    std::vector<std::string> lib_files_;
    Context *context;
};

#endif  // DUSK_MODULE_HH
