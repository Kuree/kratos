#include <pybind11/functional.h>
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>
#include "../src/tb.hh"

namespace py = pybind11;

// exception module
void init_tb(py::module &m) {
    using namespace kratos;
    py::class_<TestBench>(m, "TestBench")
        .def(py::init<Context *, const std::string &>())
        .def("var", py::overload_cast<const std::string &, uint32_t>(&TestBench::var),
             py::return_value_policy::reference)
        .def("var", py::overload_cast<const std::string &, uint32_t, uint32_t>(&TestBench::var),
             py::return_value_policy::reference)
        .def("var",
             py::overload_cast<const std::string &, uint32_t, uint32_t, bool>(&TestBench::var),
             py::return_value_policy::reference)
        .def("get_var", &TestBench::get_var)
        .def("initial", &TestBench::initial)
        .def("wire", py::overload_cast<const std::shared_ptr<Var> &, const std::shared_ptr<Port> &>(
                         &TestBench::wire))
        .def("wire",
             py::overload_cast<std::shared_ptr<Port> &, std::shared_ptr<Port> &>(&TestBench::wire))
        .def("wire", py::overload_cast<const std::shared_ptr<Var> &, const std::shared_ptr<Var> &>(
                         &TestBench::wire))
        .def("add_child_generator", &TestBench::add_child_generator)
        .def("property", &TestBench::property)
        .def("codegen", &TestBench::codegen)
        .def("top", &TestBench::top);

    py::class_<AssertValueStmt, Stmt, std::shared_ptr<AssertValueStmt>>(m, "AssertValueStmt")
        .def(py::init<const std::shared_ptr<Var> &>())
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
        .def("__repr__", &Sequence::to_string)
        .def("next", &Sequence::next, py::return_value_policy::reference);

    py::class_<Property, std::shared_ptr<Property>>(m, "Property")
        .def(py::init<std::string, std::shared_ptr<Sequence>>())
        .def("property_name", &Property::property_name)
        .def("sequence", &Property::sequence)
        .def("edge",
             py::overload_cast<BlockEdgeType, const std::shared_ptr<Var> &>(&Property::edge))
        .def("edge", [](const Property &property) { return property.edge(); });
}