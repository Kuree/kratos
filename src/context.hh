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
    std::unordered_map<std::string, std::vector<std::unique_ptr<Module>>> modules_;

public:
    Context() = default;

    Module &module(const std::string &name);
};

#endif  // DUSK_CONTEXT_HH
