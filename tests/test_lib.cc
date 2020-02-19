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
    fix_assignment_type(sram.get());
    verify_assignments(sram.get());
    verify_generator_connectivity(sram.get());
    hash_generators_parallel(sram.get());
    auto result = generate_verilog(sram.get());
    EXPECT_EQ(result.size(), 1);
    EXPECT_TRUE(result.find("sram_stub") != result.end());
    EXPECT_TRUE(is_valid_verilog(result));
}

TEST(lib, single_port_sram_array) {  // NOLINT
    Context c;
    auto sram_bank = std::make_shared<SinglePortSRAM>(&c, "sram_stub", 5, 16, true);
    auto sram = std::make_shared<SinglePortSRAM>(&c, "Memory", 16 * 64, sram_bank);
    fix_assignment_type(sram.get());
    verify_assignments(sram.get());
    verify_generator_connectivity(sram.get());
    create_module_instantiation(sram.get());
    hash_generators_parallel(sram.get());
    uniquify_generators(sram.get());
    auto result = generate_verilog(sram.get());
    EXPECT_EQ(result.size(), 2);
    EXPECT_TRUE(is_valid_verilog(result));
}

}  // namespace kratos::asic
