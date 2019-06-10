#include <utility>

#ifndef DUSK_MODULE_HH
#define DUSK_MODULE_HH
#include <map>
#include <string>
#include <unordered_map>
#include <vector>

#include "expr.hh"
#include "port.hh"

// all the variables and expressions are scoped to the module
// that's why we put the definition here

class Module;
struct Expr;

struct Var {
public:
    Var(Module *parent, std::string name, uint32_t width, bool is_signed);

    std::string name;
    uint32_t width;
    bool is_signed;

    // overload all the operators
    // unary
    Expr operator~();
    Expr operator-();
    Expr operator+();
    // binary
    Expr operator+(const Var &var);
    Expr operator-(const Var &var);
    Expr operator*(const Var &var);
    Expr operator%(const Var &var);
    Expr operator/(const Var &var);
    Expr operator>>(const Var &var);
    Expr operator<<(const Var &var);
    Expr ashr(const Var &var);

    Module *parent;

protected:
    Var(): name(), width(), is_signed(false), parent(nullptr) {}

private:
    std::pair<Var*, Var*> get_binary_var_ptr(const Var &var);
};


struct Expr : public Var {
    ExprOp op;
    Var *left;
    Var *right;
    Expr(ExprOp op, Var *left, Var *right);

};


class Module {
public:
    std::string name;
    std::map<std::string, Port> ports;

    static Module from_verilog(const std::string &src_file, const std::string &top_name,
                               const std::vector<std::string> &lib_files,
                               const std::map<std::string, PortType> &port_types);

    explicit Module(std::string name) : name(std::move(name)) {}

    void add_port(const Port &port) { ports.emplace(port.name, port); }

    Var *get_var(const std::string &var_name);
    Var &var(const std::string &var_name, uint32_t width) { return var(var_name, width, false); }
    Var &var(const std::string &var_name, uint32_t width, bool is_signed);

    void add_var(const Var &var);

private:
    std::vector<std::string> lib_files_;
    std::unordered_map<std::string, Var> vars_;
};

#endif  // DUSK_MODULE_HH
