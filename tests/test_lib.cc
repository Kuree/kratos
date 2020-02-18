#include "../src/context.hh"
#include "../src/generator.hh"
#include "../src/lib.hh"
#include "../src/pass.hh"
#include "../src/util.hh"
#include "gtest/gtest.h"

namespace kratos::asic {

TEST(lib, single_port_sram) {  // NOLINT
    Context c;
    auto sram = std::make_shared<SinglePortSRAM>(&c, "sram_stub", 5, 16, true);
    auto gen = sram->generator();
    fix_assignment_type(gen);
    verify_assignments(gen);
    verify_generator_connectivity(gen);
    hash_generators_parallel(gen);
    auto result = generate_verilog(gen);
    EXPECT_EQ(result.size(), 1);
    EXPECT_TRUE(result.find("sram_stub") != result.end());
    EXPECT_TRUE(is_valid_verilog(result));
}

TEST(lib, single_port_sram_array) {  // NOLINT
    Context c;
    auto sram_bank = std::make_shared<SinglePortSRAM>(&c, "sram_stub", 5, 16, true);
    auto sram = std::make_shared<SinglePortSRAM>(&c, "Memory", 16 * 64, sram_bank);
    auto gen = sram->generator();
    fix_assignment_type(gen);
    verify_assignments(gen);
    verify_generator_connectivity(gen);
    create_module_instantiation(gen);
    hash_generators_parallel(gen);
    uniquify_generators(gen);
    auto result = generate_verilog(gen);
    EXPECT_EQ(result.size(), 2);
    EXPECT_TRUE(is_valid_verilog(result));
}

}  // namespace kratos::asic
