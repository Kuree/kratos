#ifndef KRATOS_TB_HH
#define KRATOS_TB_HH

#include "generator.hh"
#include "stmt.hh"

namespace kratos {

enum class AssertType { AssertValue, AssertProperty };

class AssertBase : public Stmt {
public:
    AssertBase() : Stmt(StatementType::Assert) {}

    virtual AssertType assert_type() = 0;
};

class Sequence {
public:
    explicit Sequence(const std::shared_ptr<Var> &var) : var_(var.get()) {}
    Sequence *imply(const std::shared_ptr<Var> &var);
    Sequence *wait(uint32_t num_clk) { return wait(num_clk, num_clk); }
    Sequence *wait(uint32_t from_num_clk, uint32_t to_num_clk);

    [[nodiscard]] std::string to_string() const;

    [[nodiscard]] const Sequence *next() const { return next_.get(); }

private:
    Var *var_;
    std::shared_ptr<Sequence> next_ = nullptr;
    Sequence *parent_ = nullptr;

    // these are inclusive
    uint32_t wait_low_ = 0;
    uint32_t wait_high_ = 0;

    [[nodiscard]] std::string wait_to_str() const;
};

class Property {
public:
    Property(std::string property_name, std::shared_ptr<Sequence> sequence);

    [[nodiscard]] const std::string &property_name() const { return property_name_; }
    Sequence *sequence() { return sequence_.get(); }
    void edge(BlockEdgeType type, const std::shared_ptr<Var> &var);
    [[nodiscard]] std::pair<Var *, BlockEdgeType> edge() const { return edge_; }

private:
    std::string property_name_;
    std::shared_ptr<Sequence> sequence_ = nullptr;
    std::pair<Var *, BlockEdgeType> edge_ = {nullptr, BlockEdgeType::Posedge};
};

class AssertValueStmt : public AssertBase {
public:
    explicit AssertValueStmt(const std::shared_ptr<Var> &expr);

    AssertType assert_type() override { return AssertType::AssertValue; }

    Var *value() const { return assert_var_; }

private:
    Var *assert_var_;
};

class AssertPropertyStmt : public AssertBase {
public:
    explicit AssertPropertyStmt(const std::shared_ptr<Property> &property);

    AssertType assert_type() override { return AssertType ::AssertProperty; }

    Property *property() { return property_; }

private:
    Property *property_;
};

class TestBench {
public:
    TestBench(Context *context, const std::string &top_name);

    // proxy methods for top module
    Var &var(const std::string &var_name, uint32_t width) { return top_->var(var_name, width); }
    Var &var(const std::string &var_name, uint32_t width, uint32_t size) {
        return top_->var(var_name, width, size);
    }
    Var &var(const std::string &var_name, uint32_t width, uint32_t size, bool is_signed) {
        return top_->var(var_name, width, size, is_signed);
    }
    std::shared_ptr<Var> get_var(const std::string &var_name) { return top_->get_var(var_name); }
    std::shared_ptr<InitialStmtBlock> initial() { return top_->initial(); }
    void add_stmt(const std::shared_ptr<Stmt> &stmt) { top_->add_stmt(stmt); }
    void wire(const std::shared_ptr<Var> &var, const std::shared_ptr<Port> &port);
    void wire(std::shared_ptr<Port> &port1, std::shared_ptr<Port> &port2);
    void wire(const std::shared_ptr<Var> &src, const std::shared_ptr<Var> &sink);

    void add_child_generator(const std::string &instance_name,
                             const std::shared_ptr<Generator> &child) {
        top_->add_child_generator(instance_name, child);
    }

    // create properties
    std::shared_ptr<Property> property(const std::string &property_name,
                                       const std::shared_ptr<Sequence> &sequence);

    std::string codegen();

    Generator *top() { return top_; }

private:
    Generator *top_;
    std::map<std::string, std::shared_ptr<Property>> properties_;
};
}  // namespace kratos

#endif  // KRATOS_TB_HH
