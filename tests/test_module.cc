#include "../src/module.hh"
#include "gtest/gtest.h"

TEST(module, load) {
    auto mod = Module::from_verilog("module1.sv", "module1", {});
    EXPECT_TRUE(mod.ports.find("f") != mod.ports.end());
    ASSERT_ANY_THROW(Module::from_verilog("module1.sv", "module3", {}));
    ASSERT_ANY_THROW(Module::from_verilog("module1.sv", "module1", {"NON_EXIST"}));
}