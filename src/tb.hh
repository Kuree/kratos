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

    void accept(IRVisitor *visitor) override { visitor->visit(this); }
};

class Sequence : public std::enable_shared_from_this<Sequence> {
public:
    explicit Sequence(const std::shared_ptr<Var> &var) : var_(var->weak_from_this()) {}
    Sequence *imply(const std::shared_ptr<Var> &var);
    Sequence *wait(uint32_t num_clk) { return wait(num_clk, num_clk); }
    Sequence *wait(uint32_t from_num_clk, uint32_t to_num_clk);

    [[nodiscard]] std::string to_string() const;

    [[nodiscard]] const Sequence *next() const { return next_.get(); }

private:
    std::weak_ptr<Var> var_;
    std::shared_ptr<Sequence> next_ = nullptr;
    std::weak_ptr<Sequence> parent_;

    // these are inclusive
    uint32_t wait_low_ = 0;
    uint32_t wait_high_ = 0;

    [[nodiscard]] std::string wait_to_str() const;

public:
    // serialization
    template <class Archive>
    inline void serialize(Archive &ar) {
        ar(cereal::defer(var_), cereal::defer(next_), cereal::defer(parent_), wait_low_,
           wait_high_);
    }
    Sequence() = default;
};

class Property : public std::enable_shared_from_this<Property> {
public:
    Property(std::string property_name, std::shared_ptr<Sequence> sequence);

    [[nodiscard]] const std::string &property_name() const { return property_name_; }
    Sequence *sequence() { return sequence_.get(); }
    void edge(BlockEdgeType type, const std::shared_ptr<Var> &var);
    [[nodiscard]] inline std::pair<Var *, BlockEdgeType> edge() const {
        return {edge_.first.lock().get(), edge_.second};
    }

private:
    std::string property_name_;
    std::shared_ptr<Sequence> sequence_ = nullptr;
    std::pair<std::weak_ptr<Var>, BlockEdgeType> edge_ = {{}, BlockEdgeType::Posedge};

public:
    // serialization
    template <class Archive>
    inline void serialize(Archive &ar) {
        ar(property_name_, cereal::defer(sequence_), cereal::defer(edge_));
    }
    Property() = default;
};

class AssertValueStmt : public AssertBase {
public:
    explicit AssertValueStmt(const std::shared_ptr<Var> &expr);
    AssertValueStmt();

    AssertType assert_type() override { return AssertType::AssertValue; }

    Var *value() const { return assert_var_.lock().get(); }

    const std::shared_ptr<Stmt> &else_() const { return else__; }
    // currently this will only be used for debugging
    // not exposed to Python
    void set_else(const std::shared_ptr<Stmt> &stmt) {
        else__ = stmt;
        stmt->set_parent(this);
    }

private:
    std::weak_ptr<Var> assert_var_;
    std::shared_ptr<Stmt> else__ = nullptr;

public:
    // serialization
    template <class Archive>
    inline void serialize(Archive &ar) {
        ar(cereal::base_class<Stmt>(this), cereal::defer(assert_var_), cereal::defer(else__));
    }
};

class AssertPropertyStmt : public AssertBase {
public:
    explicit AssertPropertyStmt(const std::shared_ptr<Property> &property);

    AssertType assert_type() override { return AssertType ::AssertProperty; }

    Property *property() { return property_.lock().get(); }

private:
    std::weak_ptr<Property> property_;

public:
    // serialization
    template <class Archive>
    inline void serialize(Archive &ar) {
        ar(cereal::base_class<Stmt>(this), property_);
    }

    AssertPropertyStmt() : AssertBase() {}
};

class TestBench {
public:
    TestBench(Context *context, const std::string &top_name);

    // proxy methods for top module
    Var &var(const std::string &var_name, uint32_t width) {
        return top_.lock()->var(var_name, width);
    }
    Var &var(const std::string &var_name, uint32_t width, uint32_t size) {
        return top_.lock()->var(var_name, width, size);
    }
    Var &var(const std::string &var_name, uint32_t width, uint32_t size, bool is_signed) {
        return top_.lock()->var(var_name, width, size, is_signed);
    }
    std::shared_ptr<Var> get_var(const std::string &var_name) {
        return top_.lock()->get_var(var_name);
    }
    std::shared_ptr<InitialStmtBlock> initial() { return top_.lock()->initial(); }
    void add_stmt(const std::shared_ptr<Stmt> &stmt) { top_.lock()->add_stmt(stmt); }
    void wire(const std::shared_ptr<Var> &var, const std::shared_ptr<Port> &port);
    void wire(std::shared_ptr<Port> &port1, std::shared_ptr<Port> &port2);
    void wire(const std::shared_ptr<Var> &src, const std::shared_ptr<Var> &sink);

    void add_child_generator(const std::string &instance_name,
                             const std::shared_ptr<Generator> &child) {
        top_.lock()->add_child_generator(instance_name, child);
    }

    // create properties
    std::shared_ptr<Property> property(const std::string &property_name,
                                       const std::shared_ptr<Sequence> &sequence);

    std::string codegen();

    Generator *top() { return top_.lock().get(); }

private:
    std::weak_ptr<Generator> top_;
    std::map<std::string, std::shared_ptr<Property>> properties_;
};
}  // namespace kratos

#endif  // KRATOS_TB_HH
