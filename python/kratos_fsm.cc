#include <pybind11/functional.h>
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>
#include "../src/fsm.hh"
#include "../src/generator.hh"

namespace py = pybind11;

void init_fsm(py::module &m) {
    using namespace kratos;
    py::class_<FSM, std::shared_ptr<FSM>>(m, "FSM")
        .def(py::init<std::string, Generator *>())
        .def(py::init<std::string, Generator *, std::shared_ptr<Var>, std::shared_ptr<Var>>())
        .def("add_state", &FSM::add_state, py::return_value_policy::reference)
        .def("get_state", &FSM::get_state, py::return_value_policy::reference)
        .def("set_start_state", py::overload_cast<const std::string &>(&FSM::set_start_state))
        .def("set_start_state",
             py::overload_cast<const std::shared_ptr<FSMState> &>(&FSM::set_start_state))
        .def("output", py::overload_cast<const std::string &>(&FSM::output))
        .def("output", py::overload_cast<const std::shared_ptr<Var> &>(&FSM::output))
        .def("fsm_name", &FSM::fsm_name)
        .def("outputs", &FSM::outputs)
        .def("dot_graph", py::overload_cast<>(&FSM::dot_graph))
        .def("dot_graph", py::overload_cast<const std::string &>(&FSM::dot_graph))
        .def("output_table", py::overload_cast<>(&FSM::output_table))
        .def("output_table", py::overload_cast<const std::string &>(&FSM::output_table));

    py::class_<FSMState, std::shared_ptr<FSMState>>(m, "FSMState")
        .def("next", &FSMState::next)
        .def("output",
             py::overload_cast<const std::shared_ptr<Var> &, const std::shared_ptr<Var> &>(
                 &FSMState::output))
        .def("output", py::overload_cast<const std::shared_ptr<Var> &, int64_t>(&FSMState::output))
        .def_property_readonly("name", &FSMState::name);
}