#include <utility>

#ifndef DUSK_MODULE_HH
#define DUSK_MODULE_HH
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

    Expr &expr(ExprOp op, const std::shared_ptr<Var> &left, const std::shared_ptr<Var> &right);

    // ports and vars
    std::shared_ptr<Port> get_port(const std::string &port_name);
    std::shared_ptr<Var> get_var(const std::string &var_name);
    const std::set<std::string> &get_port_names() const { return ports_; }
    const std::unordered_map<std::string, std::shared_ptr<Var>> &vars() const { return vars_; }

    void remove_var(const std::string &var_name) {
        if (vars_.find(var_name) != vars_.end()) vars_.erase(var_name);
    }
    void rename_var(const std::string &old_name, const std::string &new_name);

    // statements
    void add_stmt(std::shared_ptr<Stmt> stmt);
    uint64_t stmts_count() { return stmts_.size(); }
    std::shared_ptr<Stmt> get_stmt(uint32_t index) {
        return index < stmts_.size() ? stmts_[index] : nullptr;
    }
    void remove_stmt(const std::shared_ptr<Stmt> &stmt);

    // child generator. needed for generator merge
    void add_child_generator(const std::shared_ptr<Generator> &child, bool merge);
    void remove_child_generator(const std::shared_ptr<Generator> &child);
    std::set<std::shared_ptr<Generator>> &get_child_generators() { return children_; }
    void accept_generator(ASTVisitor *visitor) { visitor->visit_generator(this); }
    bool should_child_inline(Generator *generator) const {
        return should_child_inline_.at(generator->shared_from_this());
    }
    void set_child_inline(Generator *generator, bool value) {
        should_child_inline_[generator->shared_from_this()] = value;
    }

    // if imported from verilog
    bool external() { return !lib_files_.empty(); }

    // AST stuff
    void accept(ASTVisitor *visitor) override { visitor->visit(this); }
    uint64_t child_count() override { return stmts_count(); }
    ASTNode *get_child(uint64_t index) override;

    std::unordered_set<std::string> get_vars();

    std::string get_unique_variable_name(const std::string &prefix, const std::string &var_name);

    Context *context() const { return context_; }

private:
    std::vector<std::string> lib_files_;
    Context *context_;

    std::unordered_map<std::string, std::shared_ptr<Var>> vars_;
    std::set<std::string> ports_;

    std::vector<std::shared_ptr<Stmt>> stmts_;

    std::set<std::shared_ptr<Generator>> children_;
    std::map<std::shared_ptr<Generator>, bool> should_child_inline_;
};

#endif  // DUSK_MODULE_HH22
