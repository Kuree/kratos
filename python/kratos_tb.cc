#include <pybind11/functional.h>
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>

#include "../src/tb.hh"

namespace py = pybind11;

// test bench module
void init_tb(py::module &m) {
    using namespace kratos;
    py::class_<TestBench, std::shared_ptr<TestBench>, Generator>(m, "TestBench")
        .def(py::init<Context *, const std::string &>());

    py::class_<AssertValueStmt, Stmt, std::shared_ptr<AssertValueStmt>>(m, "AssertValueStmt")
        .def(py::init<const std::shared_ptr<Var> &>())
        .def(py::init<>())
        .def("value", &AssertValueStmt::value);

    py::class_<AssertPropertyStmt, Stmt, std::shared_ptr<AssertPropertyStmt>>(m,
                                                                              "AssertPropertyStmt")
        .def(py::init<const std::shared_ptr<Property> &>())
        .def("property", &AssertPropertyStmt::property);

    py::class_<Sequence, std::shared_ptr<Sequence>>(m, "Sequence")
        .def(py::init<const std::shared_ptr<Var> &>())
        .def("imply", &Sequence::imply, py::return_value_policy::reference)
        .def("wait", py::overload_cast<uint32_t>(&Sequence::wait),
             py::return_value_policy::reference)
        .def("wait", py::overload_cast<uint32_t, uint32_t>(&Sequence::wait),
             py::return_value_policy::reference)
        .def("__repr__", [](const Sequence &seq) { return seq.to_string(); })
        .def("next", &Sequence::next, py::return_value_policy::reference);

    py::class_<Property, std::shared_ptr<Property>>(m, "Property")
        .def(py::init<std::string, std::shared_ptr<Sequence>>())
        .def("property_name", &Property::property_name)
        .def("sequence", &Property::sequence)
        .def("edge",
             py::overload_cast<EventEdgeType, const std::shared_ptr<Var> &>(&Property::edge))
        .def("edge", [](const Property &property) { return property.edge(); })
        .def_property("action", &Property::action, &Property::set_action);
}