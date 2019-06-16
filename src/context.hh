#ifndef DUSK_CONTEXT_HH
#define DUSK_CONTEXT_HH

#include <map>
#include <memory>
#include <unordered_map>
#include <vector>

struct Port;
class Module;
struct Expr;
struct Var;
struct VarSlice;

class Context {
private:
    std::unordered_map<std::string, std::unique_ptr<Var>> vars_;
    std::unordered_map<std::string, std::vector<std::unique_ptr<Module>>> modules_;

public:
    Context() = default;

    Var &var(const std::string &var_name, uint32_t width);
    Var &var(const std::string &var_name, uint32_t width, bool is_signed);

    Var *get_var(const std::string &var_name);
    void add_expr(const Expr &expr);

    Module &module(const std::string &name);
};

#endif  // DUSK_CONTEXT_HH
