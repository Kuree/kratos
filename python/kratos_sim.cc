#include <pybind11/functional.h>
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>
#include "../src/sim.hh"

namespace py = pybind11;

// simulator module
void init_simulator(py::module &m) {
    using namespace kratos;
    py::class_<Simulator>(m, "Simulator")
        .def(py::init<Generator *>())
        .def("set", py::overload_cast<Var *, std::optional<uint64_t>>(&Simulator::set))
        .def("set", py::overload_cast<Var *, const std::optional<std::vector<uint64_t>> &>(
                        &Simulator::set))
        .def("set", py::overload_cast<Var *, std::optional<int64_t>>(&Simulator::set_i))
        .def("set", py::overload_cast<Var *, const std::optional<std::vector<int64_t>> &>(
                        &Simulator::set_i))
        .def("get", &Simulator::get)
        .def("get_array", &Simulator::get_array);
}