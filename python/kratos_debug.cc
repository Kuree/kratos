#include <pybind11/functional.h>
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>
#include "../src/debug.hh"
#include "../src/generator.hh"

namespace py = pybind11;

void init_debug(py::module &m) {
    using namespace kratos;
    m.def("inject_debug_break_points", &inject_debug_break_points)
        .def("extract_debug_break_points", &extract_debug_break_points)
        .def("inject_clock_break_points",
             py::overload_cast<Generator *>(&inject_clock_break_points))
        .def("inject_clock_break_points",
             py::overload_cast<Generator *, const std::string &>(&inject_clock_break_points))
        .def("inject_clock_break_points",
             py::overload_cast<Generator *, const std::shared_ptr<Port> &>(
                 &inject_clock_break_points))
        .def("inject_assert_fail_exception", &inject_assert_fail_exception)
        .def("mock_hierarchy", &mock_hierarchy);

    py::class_<DebugDatabase>(m, "DebugDataBase")
        .def(py::init<>())
        .def(py::init<const std::string &>())
        // only use python extension since we're dealing with python binding
        .def("set_break_points", py::overload_cast<Generator *>(&DebugDatabase::set_break_points))
        .def("set_variable_mapping",
             py::overload_cast<const std::map<Generator *, std::map<std::string, Var *>> &>(
                 &DebugDatabase::set_variable_mapping))
        .def("set_variable_mapping",
             py::overload_cast<const std::map<Generator *, std::map<std::string, std::string>> &>(
                 &DebugDatabase::set_variable_mapping))
        .def("set_generator_connection", &DebugDatabase::set_generator_connection)
        .def("set_generator_hierarchy", &DebugDatabase::set_generator_hierarchy)
        .def("set_generator_variable", &DebugDatabase::set_generator_variable)
        .def("set_stmt_context", &DebugDatabase::set_stmt_context)
        // dump the database file
        .def("save_database", &DebugDatabase::save_database);
}