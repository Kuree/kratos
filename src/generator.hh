#include <utility>

#ifndef KRATOS_MODULE_HH
#define KRATOS_MODULE_HH
#include <map>
#include <string>
#include <unordered_map>
#include <vector>

#include "context.hh"
#include "port.hh"

namespace kratos {

class Generator : public std::enable_shared_from_this<Generator>, public IRNode {
public:
    std::string name;
    std::string instance_name;
    int generator_id = -1;

    static Generator from_verilog(Context *context, const std::string &src_file,
                                  const std::string &top_name,
                                  const std::vector<std::string> &lib_files,
                                  const std::map<std::string, PortType> &port_types);

    Generator(Context *context, const std::string &name);

    Var &var(const std::string &var_name, uint32_t width, uint32_t size);
    Var &var(const std::string &var_name, uint32_t width, const std::vector<uint32_t> &size);
    Var &var(const std::string &var_name, uint32_t width);
    Var &var(const std::string &var_name, uint32_t width, uint32_t size, bool is_signed);
    Var &var(const std::string &var_name, uint32_t width, const std::vector<uint32_t> &size,
             bool is_signed);
    Var &var(const Var &v, const std::string &var_name);
    Port &port(PortDirection direction, const std::string &port_name, uint32_t width) {
        return port(direction, port_name, width, 1);
    }
    Port &port(PortDirection direction, const std::string &port_name, uint32_t width,
               PortType type) {
        return port(direction, port_name, width, 1, type, false);
    }
    Port &port(PortDirection direction, const std::string &port_name, uint32_t width,
               uint32_t size);
    Port &port(PortDirection direction, const std::string &port_name, uint32_t width,
               const std::vector<uint32_t> &size);
    Port &port(PortDirection direction, const std::string &port_name, uint32_t width, uint32_t size,
               PortType type, bool is_signed);
    Port &port(PortDirection direction, const std::string &port_name, uint32_t width,
               const std::vector<uint32_t> &size, PortType type, bool is_signed);
    Port &port(const Port &p, bool check_param=true);
    Port &port(const Port &p, const std::string &port_name, bool check_param=true);
    Port &port(const PortPackedStruct &p, bool check_param=true);
    Port &port(const PortPackedStruct &p, const std::string &port_name, bool check_param=true);
    Port &port(const EnumPort &p, bool);
    Port &port(const EnumPort &p, const std::string &port_name, bool check_param=true);
    EnumPort &port(PortDirection direction, const std::string &port_name,
                   const std::shared_ptr<Enum> &def);
    PortPackedStruct &port_packed(PortDirection direction, const std::string &port_name,
                                  const PackedStruct &packed_struct_);
    PortPackedStruct &port_packed(PortDirection direction, const std::string &port_name,
                                  const PackedStruct &packed_struct_, uint32_t size);
    PortPackedStruct &port_packed(PortDirection direction, const std::string &port_name,
                                  const PackedStruct &packed_struct_,
                                  const std::vector<uint32_t> &size);
    VarPackedStruct &var_packed(const std::string &var_name, const PackedStruct &packed_struct_);
    VarPackedStruct &var_packed(const std::string &var_name, const PackedStruct &packed_struct_,
                                uint32_t size);
    VarPackedStruct &var_packed(const std::string &var_name, const PackedStruct &packed_struct_,
                                const std::vector<uint32_t> &size);
    Param &parameter(const std::string &parameter_name);
    Param &parameter(const std::string &parameter_name, uint32_t width);
    Param &parameter(const std::string &parameter_name, uint32_t width, bool is_signed);
    Param &parameter(const std::string &parameter_name, const std::shared_ptr<Enum> &enum_def);
    Param &parameter(const std::shared_ptr<Param> &param, const std::string &parameter_name);
    Enum &enum_(const std::string &enum_name, const std::map<std::string, uint64_t> &definition,
                uint32_t width);
    EnumVar &enum_var(const std::string &var_name, const std::shared_ptr<Enum> &enum_def);
    FSM &fsm(const std::string &fsm_name);
    FSM &fsm(const std::string &fsm_name, const std::shared_ptr<Var> &clk,
             const std::shared_ptr<Var> &reset);
    FunctionCallVar &call(const std::string &func_name,
                          const std::map<std::string, std::shared_ptr<Var>> &args);
    FunctionCallVar &call(const std::string &func_name,
                          const std::map<std::string, std::shared_ptr<Var>> &args, bool has_return);
    FunctionCallVar &call(const std::string &func_name,
                          const std::vector<std::shared_ptr<Var>> &args);

    Expr &expr(ExprOp op, Var *left, Var *right);
    void add_expr(const std::shared_ptr<Expr> &expr) { exprs_.emplace(expr); }
    // create properties
    std::shared_ptr<Property> property(const std::string &property_name,
                                       const std::shared_ptr<Sequence> &sequence);
    [[nodiscard]] const std::map<std::string, std::shared_ptr<Property>> &properties() const {
        return properties_;
    }
    void set_properties(const std::map<std::string, std::shared_ptr<Property>> &properties) {
        properties_ = properties;
    }

    // ports and vars
    std::shared_ptr<Port> get_port(const std::string &port_name) const;
    std::shared_ptr<Var> get_var(const std::string &var_name);
    const std::set<std::string> &get_port_names() const { return ports_; }
    const std::map<std::string, std::shared_ptr<Var>> &vars() const { return vars_; }
    void remove_var(const std::string &var_name);
    bool has_port(const std::string &port_name) { return ports_.find(port_name) != ports_.end(); }
    bool has_var(const std::string &var_name) { return vars_.find(var_name) != vars_.end(); }
    void remove_port(const std::string &port_name);
    void rename_var(const std::string &old_name, const std::string &new_name);
    void reindex_vars();
    void add_call_var(const std::shared_ptr<FunctionCallVar> &var);
    const inline std::map<std::string, std::shared_ptr<Param>> &get_params() const {
        return params_;
    }
    const inline std::map<std::string, std::shared_ptr<Enum>> &get_enums() const { return enums_; }
    std::shared_ptr<Param> get_param(const std::string &param_name) const;
    const std::map<std::string, std::shared_ptr<FSM>> &fsms() const { return fsms_; }
    std::shared_ptr<FunctionStmtBlock> function(const std::string &func_name);
    std::shared_ptr<DPIFunctionStmtBlock> dpi_function(const std::string &func_name);
    std::shared_ptr<BuiltInFunctionStmtBlock> builtin_function(const std::string &func_name);
    const std::map<std::string, std::shared_ptr<FunctionStmtBlock>> &functions() const {
        return funcs_;
    }
    bool inline has_function(const std::string &func_name) const {
        return funcs_.find(func_name) != funcs_.end();
    }
    std::shared_ptr<FunctionStmtBlock> get_function(const std::string &func_name) const;
    void add_function(const std::shared_ptr<FunctionStmtBlock> &func);

    // statements
    void add_stmt(std::shared_ptr<Stmt> stmt);
    uint64_t stmts_count() { return stmts_.size(); }
    std::shared_ptr<Stmt> get_stmt(uint32_t index) {
        return index < stmts_.size() ? stmts_[index] : nullptr;
    }
    void remove_stmt(const std::shared_ptr<Stmt> &stmt);
    const std::vector<std::shared_ptr<Stmt>> &get_all_stmts() const { return stmts_; }
    void set_stmts(const std::vector<std::shared_ptr<Stmt>> &stmts) { stmts_ = stmts; }

    // interfaces
    std::shared_ptr<InterfaceRef> interface(const std::shared_ptr<IDefinition> &def,
                                            const std::string &interface_name, bool is_port);

    // helper function to initiate the blocks
    std::shared_ptr<SequentialStmtBlock> sequential();
    std::shared_ptr<CombinationalStmtBlock> combinational();
    std::shared_ptr<InitialStmtBlock> initial();
    std::shared_ptr<LatchStmtBlock> latch();

    // child generator. needed for generator merge
    void add_child_generator(const std::string &instance_name,
                             const std::shared_ptr<Generator> &child);
    void add_child_generator(const std::string &instance_name, Generator &child);
    void add_child_generator(const std::string &instance_name,
                             const std::shared_ptr<Generator> &child,
                             const std::pair<std::string, uint32_t> &debug_info);
    Generator *get_child_generator(const std::string &instance_name_);
    void remove_child_generator(const std::shared_ptr<Generator> &child);
    std::vector<std::shared_ptr<Generator>> get_child_generators();
    uint64_t inline get_child_generator_size() const { return children_.size(); }
    bool has_child_generator(const std::shared_ptr<Generator> &child);
    bool has_child_generator(const std::string &child_name);
    void rename_child_generator(const std::shared_ptr<Generator> &child,
                                const std::string &new_name);
    void accept_generator(IRVisitor *visitor) { visitor->visit(this); }

    // AST stuff
    void accept(IRVisitor *visitor) override;
    uint64_t inline child_count() override {
        return is_external_? 0: stmts_count() + funcs_.size() + get_child_generator_size();
    }
    IRNode *get_child(uint64_t index) override;

    std::vector<std::string> get_vars();

    std::vector<std::string> get_all_var_names();

    std::string get_unique_variable_name(const std::string &prefix, const std::string &var_name);

    Context *context() const { return context_; }

    IRNode *parent() override { return parent_generator_; }
    const Generator *parent_generator() const { return parent_generator_; }
    Generator *parent_generator() { return parent_generator_; }

    bool is_stub() const { return is_stub_; }
    void set_is_stub(bool value) { is_stub_ = value; }

    // if imported from verilog or specified
    bool external() const { return (!lib_files_.empty()) || is_external_; }
    std::string external_filename() const { return lib_files_.empty() ? "" : lib_files_[0]; }
    void set_external(bool value) { is_external_ = value; }

    std::shared_ptr<Stmt> wire_ports(std::shared_ptr<Port> &port1, std::shared_ptr<Port> &port2);
    std::pair<bool, bool> correct_wire_direction(const std::shared_ptr<Var> &var1,
                                                 const std::shared_ptr<Var> &var2);
    void wire_interface(const std::shared_ptr<InterfaceRef> &inst1,
                        const std::shared_ptr<InterfaceRef> &inst2);
    void wire(Var &left, Var &right);
    void unwire(Var &var1, Var &var2);

    bool debug = false;

    const std::unordered_set<std::shared_ptr<Generator>> &get_clones() const { return clones_; }
    std::shared_ptr<Generator> clone();
    bool is_cloned() const { return is_cloned_; }
    // this is for internal libraries only. use it only if you know what you're doing
    void set_is_cloned(bool value) { is_cloned_ = value; }

    // useful passes on generator itself
    void replace(const std::string &child_name, const std::shared_ptr<Generator> &new_child);
    void replace(const std::string &child_name, const std::shared_ptr<Generator> &new_child,
                 const std::pair<std::string, uint32_t> &debug_info);

    std::vector<std::string> get_ports(PortType type) const;
    // port bundles
    bool inline has_port_bundle(const std::string &port_name) {
        return port_bundle_mapping_.find(port_name) != port_bundle_mapping_.end();
    }
    std::shared_ptr<PortBundleRef> add_bundle_port_def(const std::string &port_name,
                                                       const PortBundleDefinition &def);
    std::shared_ptr<PortBundleRef> add_bundle_port_def(
        const std::string &port_name, const PortBundleDefinition &def,
        const std::pair<std::string, uint32_t> &debug_info);
    std::shared_ptr<PortBundleRef> get_bundle_ref(const std::string &port_name);
    const std::map<std::string, std::shared_ptr<PortBundleRef>> &port_bundle_mapping() const {
        return port_bundle_mapping_;
    }
    void remove_bundle_port_ref(const std::string &ref_name) {
        port_bundle_mapping_.erase(ref_name);
    }

    // debug info
    const std::unordered_map<std::string, std::pair<std::string, uint32_t>> &children_debug()
        const {
        return children_debug_;
    }
    std::string get_child_comment(const std::string &child_name) const;
    void set_child_comment(const std::string &child_name, const std::string &comment);

    ~Generator() override = default;

    // meta functions
    bool inline has_named_block(const std::string &block_name) const {
        return named_blocks_.find(block_name) != named_blocks_.end();
    }
    std::shared_ptr<StmtBlock> get_named_block(const std::string &block_name) const;
    std::optional<std::string> get_block_name(const Stmt * stmt) const;
    void add_named_block(const std::string &block_name, const std::shared_ptr<StmtBlock> &block);
    std::unordered_set<std::string> named_blocks_labels() const;
    Generator *def_instance() const { return def_instance_; }
    void set_def_instance(Generator *def) { def_instance_ = def; }
    std::string handle_name() const;
    std::string handle_name(bool ignore_top) const;
    std::shared_ptr<Var> get_auxiliary_var(uint32_t width, bool signed_ = false);
    bool has_instantiated() const { return has_instantiated_; }
    bool &has_instantiated() { return has_instantiated_; }
    const std::map<std::string, std::shared_ptr<InterfaceRef>> &interfaces() const {
        return interfaces_;
    }
    void add_raw_import(const std::string &pkg_name) { raw_package_imports_.emplace(pkg_name); }
    const std::unordered_set<std::string> &raw_package_imports() const {
        return raw_package_imports_;
    }
    ModuleInstantiationStmt *instantiation_stmt() const { return instantiation_stmt_; }
    void set_instantiation_stmt(ModuleInstantiationStmt *stmt) { instantiation_stmt_ = stmt; }

    // used for to find out which verilog file it generates to
    std::string verilog_fn;

private:
    std::vector<std::string> lib_files_;
    Context *context_;

    std::map<std::string, std::shared_ptr<Var>> vars_;
    std::set<std::string> ports_;
    std::map<std::string, std::shared_ptr<Param>> params_;
    std::unordered_set<std::shared_ptr<Expr>> exprs_;
    std::map<std::string, std::shared_ptr<PortBundleRef>> port_bundle_mapping_;

    std::vector<std::shared_ptr<Stmt>> stmts_;

    std::unordered_map<std::string, std::shared_ptr<Generator>> children_;
    std::vector<std::string> children_names_;
    std::unordered_map<std::string, std::pair<std::string, uint32_t>> children_debug_;
    std::unordered_map<std::string, std::string> children_comments_;

    Generator *parent_generator_ = nullptr;

    bool is_stub_ = false;
    bool is_external_ = false;

    // used for shallow cloning
    std::unordered_set<std::shared_ptr<Generator>> clones_;
    bool is_cloned_ = false;

    // used to identify whether a module instantiation is created
    bool has_instantiated_ = false;

    // meta values
    // named blocks
    std::unordered_map<std::string, std::shared_ptr<StmtBlock>> named_blocks_;
    // enums
    std::map<std::string, std::shared_ptr<Enum>> enums_;
    // fsms
    std::map<std::string, std::shared_ptr<FSM>> fsms_;
    // functions
    std::map<std::string, std::shared_ptr<FunctionStmtBlock>> funcs_;
    std::map<uint32_t, std::string> func_index_;
    // function_calls
    std::set<std::shared_ptr<FunctionCallVar>> calls_;
    // cloned ref
    Generator *def_instance_ = nullptr;
    // auxiliary var
    std::unordered_map<uint32_t, std::shared_ptr<Var>> auxiliary_vars_;
    // interfaces
    std::map<std::string, std::shared_ptr<InterfaceRef>> interfaces_;
    // properties
    std::map<std::string, std::shared_ptr<Property>> properties_;

    // raw imports. only used when interfacing foreign IPs
    std::unordered_set<std::string> raw_package_imports_;

    // used to trace instantiation stmt, if any
    ModuleInstantiationStmt *instantiation_stmt_ = nullptr;

    // helper functions
    void check_param_name_conflict(const std::string &parameter_name);
};

}  // namespace kratos

#endif  // KRATOS_MODULE_HH
