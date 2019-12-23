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
struct VarVarSlice;
struct VarConcat;
struct VarExtend;
struct VarCasted;
struct Port;
struct PortBundleDefinition;
struct PortBundleRef;
struct PortPackedStruct;
struct VarPackedStruct;
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
class InterfaceInstantiationStmt;
class AssertBase;
class FSM;
enum AssignmentType : int;
enum HashStrategy : int;
struct IDefinition;
struct InterfaceModPortDefinition;
struct InterfaceDefinition;
struct InterfaceRef;

class Context {
private:
    std::unordered_map<std::string, std::set<std::shared_ptr<Generator>>> modules_;
    std::unordered_map<const Generator*, uint64_t> generator_hash_;
    int max_instance_id_ = 0;
    int max_stmt_id_ = 0;

    // hold enum definition
    std::map<std::string, std::shared_ptr<Enum>> enum_defs_;

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

    // managing the id for multiple invocation of dump database
    int &max_instance_id() { return max_instance_id_; }
    int &max_stmt_id() { return max_stmt_id_; }
    void reset_id();

    // for debugging
    uint64_t hash_table_size() const { return generator_hash_.size(); }

    void change_generator_name(Generator* generator, const std::string& new_name);
    bool generator_name_exists(const std::string& name) const;
    std::set<std::shared_ptr<Generator>> get_generators_by_name(const std::string& name) const;
    std::unordered_set<std::string> get_generator_names() const;

    const std::map<std::string, std::shared_ptr<Enum>> &enum_defs() const { return enum_defs_; }
    std::map<std::string, std::shared_ptr<Enum>> &enum_Defs() { return enum_defs_; }
    Enum &enum_(const std::string &enum_name, const std::map<std::string, uint64_t> &definition,
                uint32_t width);
    void reset_enum();

    void clear();
};

}  // namespace kratos
#endif  // KRATOS_CONTEXT_HH
