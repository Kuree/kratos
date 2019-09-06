#include <pybind11/functional.h>
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>
#include "../src/debug.hh"
#include "../src/generator.hh"

namespace py = pybind11;

void init_debug(py::module &m) {
    using namespace kratos;
    m.def("inject_debug_break_points", &inject_debug_break_points)
    .def("insert_debugger_setup", &insert_debugger_setup);
}