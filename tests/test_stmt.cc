#include "../src/context.hh"
#include "../src/generator.hh"
#include "../src/stmt.hh"
#include "gtest/gtest.h"

TEST(stmt, assign) {  // NOLINT
    Context c;
    auto &mod = c.generator("test");
    auto &var1 = mod.var("a", 2);
    auto &var2 = mod.var("b", 2, true);
    auto &var3 = mod.var("c", 4);
    auto &var4 = mod.var("d", 4);
    EXPECT_ANY_THROW(var1.assign(var2));
    EXPECT_ANY_THROW(var1.assign(var3));
    auto &stmt = var4.assign(var3);
    mod.add_stmt(stmt.shared_from_this());
    EXPECT_EQ(mod.stmts_count(), 1);
    auto stmt_ptr = mod.get_stmt(0)->as<AssignStmt>();
    EXPECT_EQ(stmt_ptr, stmt.shared_from_this());

    // try slice assign
    EXPECT_NO_THROW(var1.assign(var3[{1, 0}]));
}