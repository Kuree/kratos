#include <pybind11/functional.h>
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>
#include "../src/except.hh"

namespace py = pybind11;

// exception module
void init_except(py::module &m) {
    using namespace kratos;
    auto except_m = m.def_submodule("exception");
    py::register_exception<VarException>(except_m, "VarException");
    py::register_exception<StmtException>(except_m, "StmtException");
    py::register_exception<InternalException>(except_m, "InterException");
    py::register_exception<UserException>(except_m, "UserException");
}