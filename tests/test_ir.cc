#include "../src/context.hh"
#include "../src/expr.hh"
#include "../src/generator.hh"
#include "../src/stmt.hh"
#include "gtest/gtest.h"

using namespace kratos;

class VarVisitor : public IRVisitor {
public:
    uint32_t max_level = 0;
    VarVisitor() : IRVisitor(), vars() {}
    void visit(Var *var) override {
        if (max_level < level) max_level = level;
        vars.emplace_back(var);
    }
    std::vector<Var *> vars;
    uint32_t current_level() { return level; }
};

TEST(ir, visit_var) {  // NOLINT
    Context c;
    auto &mod = c.generator("test");
    auto &var1 = mod.var("a", 2);
    auto &var2 = mod.var("b", 2);

    auto expr = var1.assign(var2);

    VarVisitor visitor;
    visitor.visit_root(expr->ast_node());
    EXPECT_EQ(visitor.vars.size(), 2);
    EXPECT_EQ(visitor.vars[0], &var1);
    EXPECT_EQ(visitor.vars[1], &var2);
}

TEST(ir, visit_if) {  // NOLINT
    Context c;
    auto &mod = c.generator("test");
    auto &var1 = mod.var("a", 2);
    auto &var2 = mod.var("b", 2);

    auto if_stmt = IfStmt(var1.eq(var2));
    if_stmt.add_then_stmt(var1.assign(constant(2, 2)));
    if_stmt.add_else_stmt(var2.assign(constant(2, 2)));

    VarVisitor visitor;
    visitor.visit_root(if_stmt.ast_node());
    EXPECT_EQ(visitor.vars.size(), 2);
    EXPECT_EQ(visitor.max_level, 2);
    EXPECT_EQ(visitor.current_level(), 0);
}

TEST(ir, attribute) {  // NOLINT
    class TestAttribute {
    public:
        explicit TestAttribute(int value) : value_(value) {}
        int value() { return value_; }

    private:
        int value_;
    };

    Context c;
    auto &mod = c.generator("test");
    auto &var1 = mod.var("a", 2);
    auto attr = std::make_shared<Attribute>();
    attr->set(std::make_shared<TestAttribute>(42));
    var1.add_attribute(attr);
    EXPECT_EQ(var1.get_attributes().size(), 1);
    EXPECT_EQ(reinterpret_cast<TestAttribute*>(var1.get_attributes()[0]->get())->value(), 42);
}