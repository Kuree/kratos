#ifndef DUSK_CONTEXT_HH
#define DUSK_CONTEXT_HH

#include <map>
#include <memory>
#include <unordered_map>
#include <set>

struct Port;
class Generator;
struct Expr;
struct Var;
struct Const;
struct VarSlice;
class Stmt;
class AssignStmt;
class IfStmt;
class SwitchStmt;
class StmtBlock;
class CombinationalStmtBlock;
class SequentialStmtBlock;
enum AssignmentType: int;

class Context {
private:
    std::unordered_map<std::string, std::set<std::shared_ptr<Generator>>> modules_;

public:
    Context() = default;

    Generator &generator(const std::string &name);

    void remove(Generator* generator);
};

#endif  // DUSK_CONTEXT_HH
