import _kratos
from .generator import Generator


class SinglePortSRAM(Generator):
    def __init__(self, macro_name: str, data_width: int, addr_width: int,
                 partial_write: bool = False, is_clone=False, sram_def=None):
        if sram_def is None:
            self.sram = _kratos.lib.SinglePortSRAM(Generator.get_context(),
                                                   macro_name,
                                                   addr_width, data_width,
                                                   partial_write)
        else:
            self.sram = sram_def
        Generator.__init__(self, macro_name, is_clone=is_clone,
                           internal_generator=self.sram)

    # proxy for properties
    @property
    def num_ports(self):
        return self.sram.num_ports

    @property
    def addr_width(self):
        return self.sram.addr_width

    @property
    def data_width(self):
        return self.sram.data_width

    @property
    def capacity(self):
        return self.sram.capacity()

    # ports
    # to change the name
    # simply rename the port, e.g. sram.output_data.name = "Q_DATA"
    @property
    def output_data(self):
        return self.sram.output_data

    @property
    def chip_enable(self):
        return self.sram.chip_enable

    @property
    def write_enable(self):
        return self.sram.write_enable

    @property
    def addr(self):
        return self.sram.addr

    @property
    def input_data(self):
        return self.sram.input_data

    @property
    def partial_write_mask(self):
        return self.partial_write_mask


def bank_sram(generator_name, capacity, sram_def):
    if isinstance(sram_def, SinglePortSRAM):
        sram_def = sram_def.sram
    else:
        assert isinstance(sram_def, _kratos.lib.SinglePortSRAM)
    sram = _kratos.lib.SinglePortSRAM(Generator.get_context(), generator_name,
                                      capacity, sram_def)
    # allow nested sram banks
    return SinglePortSRAM(generator_name, sram.data_width, sram.addr_width,
                          sram.partial_write, False, sram_def=sram)
