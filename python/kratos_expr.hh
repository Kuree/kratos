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
        .def("add_attribute",
             [](K &obj, const std::string &value) {
                 auto attr = std::make_shared<kratos::Attribute>();
                 attr->type_str = "Python";
                 attr->value_str = value;
                 obj.add_attribute(attr);
             })
        .def("get_attributes", &K::get_attributes, py::return_value_policy::reference)
        .def("has_attribute", &K::has_attribute)
        .def_property_readonly("attributes", &K::get_attributes, py::return_value_policy::reference)
        .def("find_attribute",
             [](K &node, const std::function<bool(std::shared_ptr<kratos::Attribute>)> &func) {
                 auto const &attributes = node.get_attributes();
                 std::vector<std::shared_ptr<kratos::Attribute>> result;
                 for (auto const &attr : attributes) {
                     if (func(attr)) result.emplace_back(attr);
                 }
                 return result;
             });
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
    if (var.parametrized()) c.set_width_param(var.width_param());
    return c;
}

#endif  // KRATOS_KRATOS_EXPR_HH
