#ifndef KRATOS_CONTEXT_HH
#define KRATOS_CONTEXT_HH

#include <map>
#include <memory>
#include <set>
#include <unordered_map>
#include <unordered_set>

struct Port;
class Generator;
struct Expr;
struct Var;
struct Const;
struct VarSlice;
struct VarConcat;
struct VarSigned;
class Stmt;
class AssignStmt;
class IfStmt;
class SwitchStmt;
class StmtBlock;
class CombinationalStmtBlock;
class SequentialStmtBlock;
class ModuleInstantiationStmt;
enum AssignmentType : int;
enum HashStrategy : int;

class Context {
private:
    std::unordered_map<std::string, std::set<std::shared_ptr<Generator>>> modules_;
    std::unordered_map<Generator*, uint64_t> generator_hash_;

public:
    Context() = default;

    Generator& generator(const std::string& name);

    void remove(Generator* generator);

    void add_hash(Generator* generator, uint64_t hash);
    bool has_hash(Generator* generator);
    uint64_t get_hash(Generator* generator);

    void change_generator_name(Generator* generator, const std::string& new_name);
    bool generator_name_exists(const std::string& name) const;
    std::set<std::shared_ptr<Generator>> get_generators_by_name(const std::string& name) const;
    std::unordered_set<std::string> get_generator_names() const;

    void clear();
};

#endif  // KRATOS_CONTEXT_HH
