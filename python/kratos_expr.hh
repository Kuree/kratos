#ifndef KRATOS_KRATOS_EXPR_HH
#define KRATOS_KRATOS_EXPR_HH
#include <pybind11/operators.h>
#include <pybind11/pybind11.h>

#include <type_traits>
#include "../src/codegen.hh"
#include "../src/except.hh"
#include "../src/expr.hh"
#include "../src/generator.hh"
#include "../src/pass.hh"
#include "../src/stmt.hh"
#include "../src/util.hh"

template <typename T, typename K>
void def_attributes(T &class_) {
    namespace py = pybind11;
    class_.def("add_attribute", &K::add_attribute)
        .def("get_attributes", &K::get_attributes, py::return_value_policy::reference);
}

template <typename T>
kratos::Const &convert_int_to_const(T &var, int64_t value) {
    bool is_signed = var.is_signed();
    uint32_t width = var.width();
    return kratos::constant(value, width, is_signed);
}

template <typename T>
kratos::Const &convert_int_to_const(int64_t value, T &var) {
    bool is_signed = var.is_signed();
    uint32_t width = var.width();
    auto &c = kratos::constant(value, width, is_signed);
    if (var.parametrized())
        c.set_width_param(var.param());
    return c;
}

#endif  // KRATOS_KRATOS_EXPR_HH
