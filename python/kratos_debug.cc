#include <pybind11/functional.h>
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>

#include "../src/debug.hh"
#include "../src/generator.hh"

namespace py = pybind11;

void init_debug(py::module &m) {
    using namespace kratos;
    m.def("mock_hierarchy", &mock_hierarchy);

    py::class_<DebugDatabase>(m, "DebugDataBase")
        .def(py::init<>())
        // only use python extension since we're dealing with python binding
        .def("set_break_points", py::overload_cast<Generator *>(&DebugDatabase::set_break_points),
             py::arg("arg"))
        .def("set_variable_mapping",
             py::overload_cast<const std::map<Generator *, std::map<std::string, Var *>> &>(
                 &DebugDatabase::set_variable_mapping),
             py::arg("mapping"))
        .def("set_variable_mapping",
             py::overload_cast<const std::map<Generator *, std::map<std::string, std::string>> &>(
                 &DebugDatabase::set_variable_mapping),
             py::arg("mapping"))
        .def("set_stmt_context", &DebugDatabase::set_stmt_context, py::arg("top"))
        // dump the database file
        .def("save_database",
             py::overload_cast<const std::string &, bool>(&DebugDatabase::save_database),
             py::arg("filename"), py::arg("override"))
        .def("save_database", py::overload_cast<const std::string &>(&DebugDatabase::save_database),
             py::arg("filename"));
}