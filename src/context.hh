#ifndef KRATOS_CONTEXT_HH
#define KRATOS_CONTEXT_HH

#include <map>
#include <memory>
#include <set>
#include <string>
#include <unordered_map>
#include <unordered_set>

namespace kratos {

struct IRNode;
struct Port;
class Generator;
struct Expr;
struct Var;
struct Const;
struct Parameter;
struct VarSlice;
struct VarConcat;
struct VarCasted;
struct Port;
struct PortBundleDefinition;
struct PortBundleRef;
struct PortPacked;
struct VarPacked;
struct Param;
struct Enum;
struct EnumConst;
struct EnumVar;
struct FunctionCallVar;
class Stmt;
class AssignStmt;
class IfStmt;
class SwitchStmt;
class StmtBlock;
class ScopedStmtBlock;
class CombinationalStmtBlock;
class SequentialStmtBlock;
class FunctionStmtBlock;
class DPIFunctionStmtBlock;
class InitialStmtBlock;
class FunctionCallStmt;
class ReturnStmt;
class ModuleInstantiationStmt;
class FSM;
enum AssignmentType : int;
enum HashStrategy : int;

class Context {
private:
    std::unordered_map<std::string, std::set<std::shared_ptr<Generator>>> modules_;
    std::unordered_map<const Generator*, uint64_t> generator_hash_;

public:
    Context() = default;

    Generator& generator(const std::string& name);
    Generator empty_generator();

    void remove(Generator* generator);
    void add(Generator* generator);

    void add_hash(const Generator* generator, uint64_t hash);
    bool has_hash(const Generator* generator) const;
    uint64_t get_hash(const Generator* generator) const;
    void inline clear_hash() { generator_hash_.clear(); }

    // for debugging
    uint64_t hash_table_size() const { return generator_hash_.size(); }

    void change_generator_name(Generator* generator, const std::string& new_name);
    bool generator_name_exists(const std::string& name) const;
    std::set<std::shared_ptr<Generator>> get_generators_by_name(const std::string& name) const;
    std::unordered_set<std::string> get_generator_names() const;

    void clear();
};

}  // namespace kratos
#endif  // KRATOS_CONTEXT_HH
