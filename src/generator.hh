#include <utility>

#ifndef DUSK_MODULE_HH
#define DUSK_MODULE_HH
#include <map>
#include <string>
#include <unordered_map>
#include <vector>

#include "context.hh"
#include "port.hh"

class Generator {
public:
    std::string name;

    static Generator from_verilog(Context *context, const std::string &src_file,
                               const std::string &top_name,
                               const std::vector<std::string> &lib_files,
                               const std::map<std::string, PortType> &port_types);

    Generator(Context *context, std::string name) : name(std::move(name)), context(context) {}

    Var &var(const std::string &var_name, uint32_t width);
    Var &var(const std::string &var_name, uint32_t width, bool is_signed);
    Port &port(PortDirection direction, const std::string &port_name, uint32_t width);
    Port &port(PortDirection direction, const std::string &port_name, uint32_t width, PortType type,
               bool is_signed);

    Expr &expr(ExprOp op, const std::shared_ptr<Var> &left, const std::shared_ptr<Var> &right);

    std::shared_ptr<Port> get_port(const std::string &port_name);
    std::shared_ptr<Var> get_var(const std::string &var_name);


private:
    std::vector<std::string> lib_files_;
    Context *context;

    std::unordered_map<std::string, std::shared_ptr<Var>> vars_;
    std::set<std::string> ports_;

};

#endif  // DUSK_MODULE_HH
