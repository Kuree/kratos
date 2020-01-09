#include <pybind11/functional.h>
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>

#include "../src/lib.hh"

namespace py = pybind11;

void init_lib(py::module &m) {
    using namespace kratos;
    using namespace kratos::asic;
    // sub module
    auto lib_m = m.def_submodule("lib");

    // define sram
    auto sram = py::class_<SRAM, std::shared_ptr<SRAM>, Generator>(lib_m, "SRAM");
    sram.def_property_readonly("num_ports", &SRAM::num_ports)
        .def_property_readonly("clock", &SRAM::clock)
        .def_property_readonly("addr_width", &SRAM::addr_width)
        .def_property_readonly("data_width", &SRAM::data_width)
        .def_property("clock_name", &SRAM::clock_name, &SRAM::set_clock_name)
        .def("capacity", &SRAM::capacity);

    // define single port sram
    auto single_sram =
        py::class_<SinglePortSRAM, std::shared_ptr<SinglePortSRAM>, SRAM>(lib_m, "SinglePortSRAM");
    single_sram.def(py::init<Context *, const std::string &, uint16_t, uint16_t, bool>())
        .def(
            py::init<Context *, const std::string &, uint32_t, std::shared_ptr<SinglePortSRAM> &>())
        .def_property_readonly("output_data", &SinglePortSRAM::output_data)
        .def_property_readonly("chip_enable", &SinglePortSRAM::chip_enable)
        .def_property_readonly("write_enable", &SinglePortSRAM::write_enable)
        .def_property_readonly("addr", &SinglePortSRAM::addr)
        .def_property_readonly("input_data", &SinglePortSRAM::input_data)
        .def_property_readonly("partial_write_mask", &SinglePortSRAM::partial_write_mask)
        .def_property("output_data_name", &SinglePortSRAM::output_data_name,
                      &SinglePortSRAM::set_output_data_name)
        .def_property("chip_enable_name", &SinglePortSRAM::chip_enable_name,
                      &SinglePortSRAM::set_chip_enable_name)
        .def_property("write_enable_name", &SinglePortSRAM::write_enable_name,
                      &SinglePortSRAM::set_write_enable_name)
        .def_property("addr_name", &SinglePortSRAM::addr_name, &SinglePortSRAM::set_addr_name)
        .def_property("input_data_name", &SinglePortSRAM::input_data_name,
                      &SinglePortSRAM::set_input_data_name)
        .def_property("partial_write_mask_name", &SinglePortSRAM::partial_write_mask_name,
                      &SinglePortSRAM::set_partial_write_mask_name)
        .def_property_readonly("partial_write", &SinglePortSRAM::partial_write);
}