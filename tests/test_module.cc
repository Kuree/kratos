#include "gtest/gtest.h"
#include "../src/module.hh"

TEST(module, load) {
    auto mod = Module::from_verilog("module1.sv", "module1", {});
}