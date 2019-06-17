#ifndef DUSK_CONTEXT_HH
#define DUSK_CONTEXT_HH

#include <map>
#include <memory>
#include <unordered_map>
#include <vector>

struct Port;
class Generator;
struct Expr;
struct Var;
struct VarSlice;

class Context {
private:
    std::unordered_map<std::string, std::vector<std::unique_ptr<Generator>>> modules_;

public:
    Context() = default;

    Generator &generator(const std::string &name);
};

#endif  // DUSK_CONTEXT_HH
