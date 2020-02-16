#include <pybind11/functional.h>
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>

#include "../src/codegen.hh"
#include "../src/generator.hh"

namespace py = pybind11;

void init_code_gen(py::module &m) {
    using namespace kratos;
    py::class_<VerilogModule>(m, "VerilogModule")
        .def(py::init<Generator *>())
        .def("verilog_src", &VerilogModule::verilog_src)
        .def("run_passes", &VerilogModule::run_passes)
        .def("pass_manager", &VerilogModule::pass_manager, py::return_value_policy::reference);

    m.def("create_wrapper_flatten", &create_wrapper_flatten, py::return_value_policy::reference)
        .def("generate_sv_package_header",
             py::overload_cast<Generator *, const std::string &, bool>(&generate_sv_package_header))
        .def("generate_sv_package_header", &generate_sv_package_header)
        .def("fix_verilog_ln", &fix_verilog_ln);
}