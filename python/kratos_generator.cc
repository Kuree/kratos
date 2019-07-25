#include <pybind11/operators.h>
#include <pybind11/pybind11.h>
#include <pybind11/functional.h>
#include <pybind11/stl.h>
#include "../src/except.hh"
#include "../src/expr.hh"
#include "../src/generator.hh"
#include "../src/stmt.hh"


namespace py = pybind11;
using std::shared_ptr;

void init_generator(py::module &m) {
    using namespace kratos;
    auto generator = py::class_<Generator, ::shared_ptr<Generator>, IRNode>(m, "Generator");
    generator.def("from_verilog", &Generator::from_verilog)
        .def("var", py::overload_cast<const std::string &, uint32_t>(&Generator::var),
             py::return_value_policy::reference)
        .def("var", py::overload_cast<const std::string &, uint32_t, bool>(&Generator::var),
             py::return_value_policy::reference)
        .def("port",
             py::overload_cast<PortDirection, const std::string &, uint32_t>(&Generator::port),
             py::return_value_policy::reference)
        .def("port",
             py::overload_cast<PortDirection, const std::string &, uint32_t, PortType, bool>(
                 &Generator::port),
             py::return_value_policy::reference)
        .def("array",
             py::overload_cast<const std::string &, uint32_t, uint32_t, bool>(&Generator::array),
             py::return_value_policy::reference)
        .def("array", py::overload_cast<const std::string &, uint32_t, uint32_t>(&Generator::array),
             py::return_value_policy::reference)
        .def("constant", py::overload_cast<int64_t, uint32_t>(&Generator::constant),
             py::return_value_policy::reference)
        .def("constant", py::overload_cast<int64_t, uint32_t, bool>(&Generator::constant),
             py::return_value_policy::reference)
        .def("parameter",
             py::overload_cast<const std::string &, uint32_t, bool>(&Generator::parameter),
             py::return_value_policy::reference)
        .def("port_packed", &Generator::port_packed, py::return_value_policy::reference)
        .def("get_params", &Generator::get_params)
        .def("get_param", &Generator::get_param)
        .def("get_port", &Generator::get_port, py::return_value_policy::reference)
        .def("get_var", &Generator::get_var, py::return_value_policy::reference)
        .def("get_port_names", &Generator::get_port_names)
        .def("vars", &Generator::vars)
        .def("add_stmt", &Generator::add_stmt)
        .def("remove_stmt", &Generator::remove_stmt)
        .def("stmts_count", &Generator::stmts_count)
        .def("get_stmt", &Generator::get_stmt)
        .def("sequential", &Generator::sequential, py::return_value_policy::reference)
        .def("combinational", &Generator::combinational, py::return_value_policy::reference)
        .def("add_child_generator",
             py::overload_cast<const std::string &, const std::shared_ptr<Generator> &>(
                 &Generator::add_child_generator))
        .def("add_child_generator",
             py::overload_cast<const std::string &, const std::shared_ptr<Generator> &,
                               const std::pair<std::string, uint32_t> &>(
                 &Generator::add_child_generator))
        .def("remove_child_generator", &Generator::remove_child_generator)
        .def("get_child_generators", &Generator::get_child_generators)
        .def("get_child_generator_size", &Generator::get_child_generator_size)
        .def("replace_child_generator", &Generator::replace_child_generator)
        .def("external", &Generator::external)
        .def("set_external", &Generator::set_external)
        .def("external_filename", &Generator::external_filename)
        .def("is_stub", &Generator::is_stub)
        .def("set_is_stub", &Generator::set_is_stub)
        .def("wire_ports", &Generator::wire_ports)
        .def("get_unique_variable_name", &Generator::get_unique_variable_name)
        .def("context", &Generator::context, py::return_value_policy::reference)
        .def_readwrite("instance_name", &Generator::instance_name)
        .def_readwrite("name", &Generator::name)
        .def_readwrite("debug", &Generator::debug)
        .def("clone", &Generator::clone)
        .def_property("is_cloned", &Generator::is_cloned, &Generator::set_is_cloned)
        .def("__contains__", &Generator::has_child_generator);

    generator.def("add_fn_ln", [](Generator &var, const std::pair<std::string, uint32_t> &info) {
        var.fn_name_ln.emplace_back(info);
    });
}