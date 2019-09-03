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

    static Generator from_verilog(Context *context, const std::string &src_file,
                                  const std::string &top_name,
                                  const std::vector<std::string> &lib_files,
                                  const std::map<std::string, PortType> &port_types);

    Generator(Context *context, const std::string &name)
        : IRNode(IRNodeKind::GeneratorKind), name(name), instance_name(name), context_(context) {}

    Var &var(const std::string &var_name, uint32_t width, uint32_t size);
    Var &var(const std::string &var_name, uint32_t width) { return var(var_name, width, 1); }
    Var &var(const std::string &var_name, uint32_t width, uint32_t size, bool is_signed);
    Port &port(PortDirection direction, const std::string &port_name, uint32_t width) {
        return port(direction, port_name, width, 1);
    }
    Port &port(PortDirection direction, const std::string &port_name, uint32_t width,
               uint32_t size);
    Port &port(PortDirection direction, const std::string &port_name, uint32_t width, uint32_t size,
               PortType type, bool is_signed);
    PortPacked &port_packed(PortDirection direction, const std::string &port_name,
                            const PackedStruct &packed_struct_);
    VarPacked &var_packed(const std::string &var_name, const PackedStruct &packed_struct_);
    Param &parameter(const std::string &parameter_name, uint32_t width);
    Param &parameter(const std::string &parameter_name, uint32_t width, bool is_signed);
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

    Expr &expr(ExprOp op, const std::shared_ptr<Var> &left, const std::shared_ptr<Var> &right);

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
    void add_call_var(const std::shared_ptr<FunctionCallVar> &var);
    const inline std::map<std::string, std::shared_ptr<Param>> &get_params() const {
        return params_;
    }
    const inline std::map<std::string, std::shared_ptr<Enum>> &get_enums() const { return enums_; }
    std::shared_ptr<Param> get_param(const std::string &param_name) const;
    const std::map<std::string, std::shared_ptr<FSM>> &fsms() const { return fsms_; }
    std::shared_ptr<FunctionStmtBlock> function(const std::string &func_name);
    std::shared_ptr<DPIFunctionStmtBlock> dpi_function(const std::string &func_name);
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

    // helper function to initiate the blocks
    std::shared_ptr<SequentialStmtBlock> sequential();
    std::shared_ptr<CombinationalStmtBlock> combinational();
    std::shared_ptr<InitialStmtBlock> initial();

    // child generator. needed for generator merge
    void add_child_generator(const std::string &instance_name,
                             const std::shared_ptr<Generator> &child);
    void add_child_generator(const std::string &instance_name,
                             const std::shared_ptr<Generator> &child,
                             const std::pair<std::string, uint32_t> &debug_info);
    void remove_child_generator(const std::shared_ptr<Generator> &child);
    std::vector<std::shared_ptr<Generator>> get_child_generators();
    uint64_t inline get_child_generator_size() const { return children_.size(); }
    bool has_child_generator(const std::shared_ptr<Generator> &child);
    bool has_child_generator(const std::string &child_name);
    void rename_child_generator(const std::shared_ptr<Generator>& child, const std::string &new_name);
    void accept_generator(IRVisitor *visitor) { visitor->visit(this); }

    // AST stuff
    void accept(IRVisitor *visitor) override;
    uint64_t inline child_count() override {
        return stmts_count() + funcs_.size() + get_child_generator_size();
    }
    IRNode *get_child(uint64_t index) override;

    std::vector<std::string> get_vars();

    std::vector<std::string> get_all_var_names();

    std::string get_unique_variable_name(const std::string &prefix, const std::string &var_name);

    Context *context() const { return context_; }

    IRNode *parent() override { return parent_generator_; }
    const Generator* parent_generator() const { return parent_generator_; }

    bool is_stub() const { return is_stub_; }
    void set_is_stub(bool value) { is_stub_ = value; }

    // if imported from verilog or specified
    bool external() { return (!lib_files_.empty()) || is_external_; }
    std::string external_filename() const { return lib_files_.empty() ? "" : lib_files_[0]; }
    void set_external(bool value) { is_external_ = value; }

    std::shared_ptr<Stmt> wire_ports(std::shared_ptr<Port> &port1, std::shared_ptr<Port> &port2);
    std::pair<bool, bool> correct_wire_direction(const std::shared_ptr<Var> &var1,
                                                 const std::shared_ptr<Var> &var2);

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
    std::shared_ptr<PortBundleRef> add_bundle_port_def(
        const std::string &port_name, const std::shared_ptr<PortBundleDefinition> &def);
    std::shared_ptr<PortBundleRef> add_bundle_port_def(
        const std::string &port_name, const std::shared_ptr<PortBundleDefinition> &def,
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
    std::shared_ptr<Var> get_null_var(const std::shared_ptr<Var> &var);
    bool inline has_named_block(const std::string &block_name) const {
        return named_blocks_.find(block_name) != named_blocks_.end();
    }
    std::shared_ptr<StmtBlock> get_named_block(const std::string &block_name) const;
    void add_named_block(const std::string &block_name, const std::shared_ptr<StmtBlock> &block);
    std::unordered_set<std::string> named_blocks_labels() const;
    Generator *def_instance() const { return def_instance_; }
    void set_def_instance(Generator *def) { def_instance_ = def; }
    std::string handle_name() const;
    std::string handle_name(bool ignore_top) const;

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
};

}  // namespace kratos

#endif  // KRATOS_MODULE_HH22
