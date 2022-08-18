#ifndef KRATOS_TB_HH
#define KRATOS_TB_HH

#include "generator.hh"
#include "stmt.hh"

#include <functional>

namespace kratos {

enum class AssertType { AssertValue, AssertProperty };

class AssertBase : public Stmt {
public:
    AssertBase() : Stmt(StatementType::Assert) {}

    virtual AssertType assert_type() = 0;

    void accept(IRVisitor *visitor) override { visitor->visit(this); }
};

class Sequence {
public:
    explicit Sequence(const std::shared_ptr<Var> &var) : var_(var.get()) {}
    Sequence *imply(const std::shared_ptr<Var> &var);
    Sequence *wait(uint32_t num_clk) { return wait(num_clk, num_clk); }
    Sequence *wait(uint32_t from_num_clk, uint32_t to_num_clk);

    [[nodiscard]] std::string to_string() const;
    [[nodiscard]] std::string to_string(const std::function<std::string(Var *)> &var_str) const;

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

enum class PropertyAction : int {
    None = 0,
    Cover = 1u << 1u,
    Assume = 1u << 2u,
    Assert = 1u << 3u
};

class Property {
public:
    Property(std::string property_name, std::shared_ptr<Sequence> sequence);

    [[nodiscard]] const std::string &property_name() const { return property_name_; }
    Sequence *sequence() { return sequence_.get(); }
    void edge(EventEdgeType type, const std::shared_ptr<Var> &var);
    [[nodiscard]] std::pair<Var *, EventEdgeType> edge() const { return edge_; }

    void set_action(PropertyAction action) { action_ = action; }
    [[nodiscard]] PropertyAction action() const { return action_; }

private:
    std::string property_name_;
    std::shared_ptr<Sequence> sequence_ = nullptr;
    std::pair<Var *, EventEdgeType> edge_ = {nullptr, EventEdgeType::Posedge};

    PropertyAction action_ = PropertyAction::None;
};

class AssertValueStmt : public AssertBase {
public:
    explicit AssertValueStmt(std::shared_ptr<Var> expr);
    AssertValueStmt();

    AssertType assert_type() override { return AssertType::AssertValue; }

    Var *value() const { return assert_var_.get(); }

    const std::shared_ptr<Stmt> &else_() const { return else_stmt_; }
    // currently this will only be used for debugging
    // not exposed to Python
    void set_else(const std::shared_ptr<Stmt> &stmt) {
        else_stmt_ = stmt;
        stmt->set_parent(this);
    }

private:
    std::shared_ptr<Var> assert_var_;
    std::shared_ptr<Stmt> else_stmt_ = nullptr;
};

class AssertPropertyStmt : public AssertBase {
public:
    explicit AssertPropertyStmt(const std::shared_ptr<Property> &property);

    AssertType assert_type() override { return AssertType ::AssertProperty; }

    Property *property() { return property_; }

    const std::shared_ptr<Stmt> &else_() const { return else_stmt_; }
    // currently this will only be used for debugging
    // not exposed to Python
    void set_else(const std::shared_ptr<Stmt> &stmt) {
        else_stmt_ = stmt;
        stmt->set_parent(this);
    }

private:
    Property *property_;
    std::shared_ptr<Stmt> else_stmt_ = nullptr;
};

class TestBench : public Generator {
public:
    TestBench(Context *context, const std::string &top_name);

    void add_port_name(const std::string &name) override;
};
}  // namespace kratos

#endif  // KRATOS_TB_HH
