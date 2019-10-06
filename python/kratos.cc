#include <pybind11/pybind11.h>
#include <pybind11/functional.h>
#include <pybind11/stl.h>
#include "../src/codegen.hh"
#include "../src/except.hh"
#include "../src/expr.hh"
#include "../src/generator.hh"
#include "../src/pass.hh"
#include "../src/stmt.hh"
#include "../src/util.hh"

#include "kratos_expr.hh"

namespace py = pybind11;
using std::shared_ptr;
using namespace kratos;

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

// util submodule
void init_util(py::module &m) {
    auto util_m = m.def_submodule("util");

    util_m
        .def("is_valid_verilog", py::overload_cast<const std::string &>(&is_valid_verilog),
             "Check if the verilog doesn't have any syntax errors. Notice that you "
             "have to have either verilator or iverilog in your $PATH to use this function")
        .def("is_valid_verilog",
             py::overload_cast<const std::map<std::string, std::string> &>(&is_valid_verilog),
             "Check if the verilog doesn't have any syntax errors. Notice that you "
             "have to have either verilator or iverilog in your $PATH to use this function")
        .def("set_num_cpus", &set_num_cpus)
        .def("get_num_cpus", &get_num_cpus);
}


void init_context(py::module &m) {
    auto context = py::class_<Context>(m, "Context");
    context.def(py::init())
        .def("generator", &Context::generator, py::return_value_policy::reference)
        .def("empty_generator", &Context::empty_generator)
        .def("clear", &Context::clear)
        .def("get_hash", &Context::get_hash)
        .def("get_generators_by_name", &Context::get_generators_by_name)
        .def("hash_table_size", &Context::hash_table_size)
        .def("change_generator_name", &Context::change_generator_name)
        .def("add", &Context::add)
        .def("has_hash", &Context::has_hash);
}


void init_code_gen(py::module &m) {
    py::class_<VerilogModule>(m, "VerilogModule")
        .def(py::init<Generator *>())
        .def("verilog_src", &VerilogModule::verilog_src)
        .def("run_passes", &VerilogModule::run_passes)
        .def("pass_manager", &VerilogModule::pass_manager, py::return_value_policy::reference);
}

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
}
