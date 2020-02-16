#include <pybind11/functional.h>
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>

#include "../src/context.hh"
#include "../src/generator.hh"

namespace py = pybind11;

void init_context(py::module &m) {
    using namespace kratos;
    auto context = py::class_<Context>(m, "Context");
    context.def(py::init())
        .def("generator", &Context::generator, py::return_value_policy::reference)
        .def("empty_generator", &Context::empty_generator)
        .def("clear", &Context::clear)
        .def("get_hash", &Context::get_hash, py::arg("internal_generator"))
        .def("get_generators_by_name", &Context::get_generators_by_name, py::arg("name"))
        .def("hash_table_size", &Context::hash_table_size)
        .def("change_generator_name", &Context::change_generator_name,
             py::arg("internal_generator"), py::arg("new_name"))
        .def("add", &Context::add, py::arg("internal_generator"))
        .def("has_hash", &Context::has_hash, py::arg("internal_generator"))
        .def("clear_hash",
             [](Context &context) {
               // the original one gives segfault for g++-8. don't know why
               context.clear_hash();
             })
        .def("enum", &Context::enum_, py::arg("enum_name"), py::arg("definition"),
             py::arg("width"));
}