#include <utility>

#ifndef KRATOS_MODULE_HH
#define KRATOS_MODULE_HH
#include <map>
#include <string>
#include <unordered_map>
#include <vector>

#include "context.hh"
#include "port.hh"

class Generator : public std::enable_shared_from_this<Generator>, public ASTNode {
public:
    std::string name;
    std::string instance_name;

    static Generator from_verilog(Context *context, const std::string &src_file,
                                  const std::string &top_name,
                                  const std::vector<std::string> &lib_files,
                                  const std::map<std::string, PortType> &port_types);

    Generator(Context *context, const std::string &name)
        : ASTNode(ASTNodeKind::GeneratorKind), name(name), instance_name(name), context_(context) {}

    Var &var(const std::string &var_name, uint32_t width);
    Var &var(const std::string &var_name, uint32_t width, bool is_signed);
    Port &port(PortDirection direction, const std::string &port_name, uint32_t width);
    Port &port(PortDirection direction, const std::string &port_name, uint32_t width, PortType type,
               bool is_signed);
    Const &constant(int64_t value, uint32_t width);
    Const &constant(int64_t value, uint32_t width, bool is_signed);
    Param &parameter(const std::string &parameter_name, uint32_t width);
    Param &parameter(const std::string &parameter_name, uint32_t width, bool is_signed);

    Expr &expr(ExprOp op, const std::shared_ptr<Var> &left, const std::shared_ptr<Var> &right);

    // ports and vars
    std::shared_ptr<Port> get_port(const std::string &port_name);
    std::shared_ptr<Var> get_var(const std::string &var_name);
    const std::set<std::string> &get_port_names() const { return ports_; }
    const std::map<std::string, std::shared_ptr<Var>> &vars() const { return vars_; }
    void remove_var(const std::string &var_name) {
        if (vars_.find(var_name) != vars_.end()) vars_.erase(var_name);
    }
    void rename_var(const std::string &old_name, const std::string &new_name);
    const inline std::map<std::string, std::shared_ptr<Param>> &get_params() const {
        return params_;
    }
    std::shared_ptr<Param> get_param(const std::string &param_name) const;

    // statements
    void add_stmt(std::shared_ptr<Stmt> stmt);
    uint64_t stmts_count() { return stmts_.size(); }
    std::shared_ptr<Stmt> get_stmt(uint32_t index) {
        return index < stmts_.size() ? stmts_[index] : nullptr;
    }
    void remove_stmt(const std::shared_ptr<Stmt> &stmt);
    // helper function to initiate the blocks
    std::shared_ptr<SequentialStmtBlock> sequential();
    std::shared_ptr<CombinationalStmtBlock> combinational();

    // child generator. needed for generator merge
    void add_child_generator(const std::shared_ptr<Generator> &child, bool merge);
    void remove_child_generator(const std::shared_ptr<Generator> &child);
    std::vector<std::shared_ptr<Generator>> &get_child_generators() { return children_; }
    uint64_t inline get_child_generator_size() const { return children_.size(); }
    bool has_child_generator(const std::shared_ptr<Generator> &child);
    void accept_generator(ASTVisitor *visitor) { visitor->visit(this); }
    bool should_child_inline(Generator *generator) const {
        return should_child_inline_.at(generator->shared_from_this());
    }
    void set_child_inline(Generator *generator, bool value) {
        should_child_inline_[generator->shared_from_this()] = value;
    }
    void replace_child_generator(const std::shared_ptr<Generator> &target,
                                 const std::shared_ptr<Generator> &new_generator);

    // AST stuff
    void accept(ASTVisitor *visitor) override;
    uint64_t inline child_count() override { return stmts_count() + get_child_generator_size(); }
    ASTNode *get_child(uint64_t index) override;

    std::set<std::string> get_vars();

    std::set<std::string> get_all_var_names();

    std::string get_unique_variable_name(const std::string &prefix, const std::string &var_name);

    Context *context() const { return context_; }

    ASTNode *parent() override { return parent_generator_; }

    bool is_stub() const { return is_stub_; }
    void set_is_stub(bool value) { is_stub_ = value; }

    // if imported from verilog or specified
    bool external() { return (!lib_files_.empty()) || is_external_; }
    std::string external_filename() const { return lib_files_.empty() ? "" : lib_files_[0]; }
    void set_external(bool value) { is_external_ = value; }

    std::shared_ptr<Stmt> wire_ports(std::shared_ptr<Port> &port1, std::shared_ptr<Port> &port2);

    bool debug = false;

    const std::unordered_set<std::shared_ptr<Generator>> &get_clones() const { return clones_; }
    std::shared_ptr<Generator> clone();
    bool is_cloned() const { return is_cloned_; }

private:
    std::vector<std::string> lib_files_;
    Context *context_;

    std::map<std::string, std::shared_ptr<Var>> vars_;
    std::set<std::string> ports_;
    std::map<std::string, std::shared_ptr<Param>> params_;

    std::vector<std::shared_ptr<Stmt>> stmts_;

    std::vector<std::shared_ptr<Generator>> children_;
    std::map<std::shared_ptr<Generator>, bool> should_child_inline_;

    Generator *parent_generator_ = nullptr;

    std::unordered_set<std::shared_ptr<Const>> consts_;

    bool is_stub_ = false;
    bool is_external_ = false;

    // used for shallow cloning
    std::unordered_set<std::shared_ptr<Generator>> clones_;
    bool is_cloned_ = false;
};

#endif  // KRATOS_MODULE_HH22
