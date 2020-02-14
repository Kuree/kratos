#include <pybind11/functional.h>
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>

#include "../src/formal.hh"


namespace py = pybind11;

void init_formal(py::module &main_m) {
    using namespace kratos;
    auto formal = main_m.def_submodule("formal");
    formal.def("remove_async_reset", &remove_async_reset);
}