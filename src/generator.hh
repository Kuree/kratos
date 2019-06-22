#include <utility>

#ifndef DUSK_MODULE_HH
#define DUSK_MODULE_HH
#include <map>
#include <string>
#include <unordered_map>
#include <vector>

#include "context.hh"
#include "port.hh"

class Generator : public ASTNode {
public:
    std::string name;

    static Generator from_verilog(Context *context, const std::string &src_file,
                                  const std::string &top_name,
                                  const std::vector<std::string> &lib_files,
                                  const std::map<std::string, PortType> &port_types);

    Generator(Context *context, std::string name) : name(std::move(name)), context(context) {}

    Var &var(const std::string &var_name, uint32_t width);
    Var &var(const std::string &var_name, uint32_t width, bool is_signed);
    Port &port(PortDirection direction, const std::string &port_name, uint32_t width);
    Port &port(PortDirection direction, const std::string &port_name, uint32_t width, PortType type,
               bool is_signed);
    Const &constant(int64_t value, uint32_t width);
    Const &constant(int64_t value, uint32_t width, bool is_signed);

    Expr &expr(ExprOp op, const std::shared_ptr<Var> &left, const std::shared_ptr<Var> &right);

    std::shared_ptr<Port> get_port(const std::string &port_name);
    std::shared_ptr<Var> get_var(const std::string &var_name);
    const std::unordered_map<std::string, std::shared_ptr<Var>> &vars() const { return vars_; }
    void remove_var(const std::string &var_name) {
        if (vars_.find(var_name) != vars_.end()) vars_.erase(var_name);
    }

    void add_stmt(std::shared_ptr<Stmt> stmt) { stmts_.emplace_back(std::move(stmt)); }

    uint64_t stmts_count() { return stmts_.size(); }
    std::shared_ptr<Stmt> get_stmt(uint32_t index) { return stmts_[index]; }

    // child generator. needed for generator merge
    void add_child_generator(const std::shared_ptr<Generator> &child) { children_.emplace(child); }
    void remove_child_generator(const std::shared_ptr<Generator> &child);

    // AST stuff
    void accept(ASTVisitor *visitor) override { visitor->visit(this); }
    uint64_t child_count() override { return stmts_count(); }
    ASTNode *get_child(uint64_t index) override;

private:
    std::vector<std::string> lib_files_;
    Context *context;

    std::unordered_map<std::string, std::shared_ptr<Var>> vars_;
    std::set<std::string> ports_;

    std::vector<std::shared_ptr<Stmt>> stmts_;

    std::set<std::shared_ptr<Generator>> children_;
};

#endif  // DUSK_MODULE_HH22
