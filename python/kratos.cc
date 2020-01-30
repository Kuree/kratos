#include <pybind11/functional.h>
#include <pybind11/pybind11.h>
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
        .def("has_hash", &Context::has_hash)
        .def("clear_hash",
             [](Context &context) {
                 // the original one gives segfault for g++-8. don't know why
                 context.clear_hash();
             })
        .def("enum", &Context::enum_);
}

void init_code_gen(py::module &m) {
    py::class_<VerilogModule>(m, "VerilogModule")
        .def(py::init<Generator *>())
        .def("verilog_src", &VerilogModule::verilog_src)
        .def("run_passes", &VerilogModule::run_passes)
        .def("pass_manager", &VerilogModule::pass_manager, py::return_value_policy::reference);

    m.def("create_wrapper_flatten", &create_wrapper_flatten, py::return_value_policy::reference)
        .def("generate_sv_package_header",
             py::overload_cast<Generator *, const std::string &, bool>(&generate_sv_package_header))
        .def("generate_sv_package_header", &generate_sv_package_header)
        .def("fix_verilog_ln", &fix_verilog_ln);
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
    init_simulator(m);
    init_interface(m);
    init_cast(m);
    init_lib(m);
    init_fault(m);
}
