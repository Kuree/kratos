#include <pybind11/functional.h>
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>


namespace py = pybind11;

void init_util(py::module &m);
void init_pass(py::module &m);
void init_generator(py::module &m);
void init_expr(py::module &m);
void init_stmt(py::module &m);
void init_enum_type(py::module &m);
void init_fsm(py::module &m);
void init_except(py::module &m);
void init_tb(py::module &m);
void init_debug(py::module &m);
void init_enum(py::module &m);
void init_python_util(py::module &m);
void init_simulator(py::module &m);
void init_interface(py::module &m);
void init_cast(py::module &m);
void init_lib(py::module &m);
void init_fault(py::module &m);
void init_formal(py::module &m);
void init_code_gen(py::module &m);
void init_context(py::module &m);
void init_event(py::module &m);


PYBIND11_MODULE(_kratos, m) {
    m.doc() = R"pbdoc(
        .. currentmodule:: _kratos
    )pbdoc";

    init_enum(m);
    init_pass(m);
    init_expr(m);
    init_context(m);
    init_generator(m);
    init_stmt(m);
    init_code_gen(m);
    init_util(m);
    init_except(m);
    init_enum_type(m);
    init_fsm(m);
    init_tb(m);
    init_debug(m);
    init_python_util(m);
    init_simulator(m);
    init_interface(m);
    init_cast(m);
    init_lib(m);
    init_fault(m);
    init_formal(m);
    init_event(m);
}
