from kratos.lib import SinglePortSRAM, bank_sram
from kratos import verilog


def test_single_port_sram(check_gold):
    s = SinglePortSRAM("SRAM_MACRO", 16, 10)
    assert s.num_ports == 1
    check_gold(s, "test_single_port_sram")


def test_single_port_sram_bank(check_gold):
    s = SinglePortSRAM("SRAM_MACRO", 16, 10)
    # bank 6 of them together
    sram = bank_sram("Memory", s.capacity * 6, s)
    assert isinstance(sram, SinglePortSRAM)
    check_gold(sram, "test_single_port_sram_bank")


if __name__ == "__main__":
    from conftest import check_gold_fn
    test_single_port_sram_bank(check_gold_fn)
