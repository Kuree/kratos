#include <pybind11/pybind11.h>
#include <pybind11/stl.h>
#include "../src/expr.hh"
#include "../src/generator.hh"
#include "../src/pass.hh"
#include "../src/stmt.hh"

namespace py = pybind11;

// pass submodule
void init_pass(py::module &m) {
    auto pass_m = m.def_submodule("pass");

    pass_m.def("fix_assignment_type", &fix_assignment_type);
}

PYBIND11_MODULE(_kratos, m) {
    m.doc() = "C++ Python binding for kratos";
    init_pass(m);
}