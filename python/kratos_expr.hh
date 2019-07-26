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
    bool is_signed = var.is_signed;
    uint32_t width = var.width;
    auto gen = var.generator;
    return gen->constant(value, width, is_signed);
}

template <typename T>
kratos::Const &convert_int_to_const(int64_t value, T &var) {
    bool is_signed = var.is_signed;
    uint32_t width = var.width;
    auto gen = var.generator;
    return gen->constant(value, width, is_signed);
}

template <typename T, typename K>
void init_getitem(T &class_) {
    namespace py = pybind11;
    class_
        .def(
            "__getitem__", [](K & k, std::pair<uint32_t, uint32_t> v) -> auto & { return k[v]; },
            py::return_value_policy::reference)
        .def(
            "__getitem__", [](K & k, uint32_t idx) -> auto & { return k[idx]; },
            py::return_value_policy::reference);
}

template <typename T, typename K>
void init_common_expr(T &class_) {
    namespace py = pybind11;
    using std::shared_ptr;
    using namespace kratos;
    // see how available object overloads here: https://docs.python.org/3/reference/datamodel.html
    class_.def("__repr__", &K::to_string)
        .def(
            "__invert__", [](const K &var) -> Expr & { return ~var; },
            py::return_value_policy::reference)
        .def(
            "__neg__", [](const K &var) -> Expr & { return -var; },
            py::return_value_policy::reference)
        .def(
            "__pos__", [](const K &var) -> Expr & { return +var; },
            py::return_value_policy::reference)
        .def(
            "__add__", [](const K &left, const Var &right) -> Expr & { return left + right; },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__add__",
            [](const K &left, const int64_t &right) -> Expr & {
                return left + convert_int_to_const(left, right);
            },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__add__",
            [](const int64_t &left, K &right) -> Expr & {
                return convert_int_to_const(left, right) + right;
            },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__sub__", [](const K &left, const Var &right) -> Expr & { return left - right; },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__sub__",
            [](const K &left, const int64_t &right) -> Expr & {
                return left - convert_int_to_const(left, right);
            },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__sub__",
            [](const int64_t &left, K &right) -> Expr & {
                return convert_int_to_const(left, right) - right;
            },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__mul__", [](const K &left, const Var &right) -> Expr & { return left * right; },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__mul__",
            [](const K &left, const int64_t &right) -> Expr & {
                return left * convert_int_to_const(left, right);
            },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__mul__",
            [](const int64_t &left, K &right) -> Expr & {
                return convert_int_to_const(left, right) * right;
            },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__mod__", [](const K &left, const Var &right) -> Expr & { return left % right; },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__mod__",
            [](const K &left, const int64_t &right) -> Expr & {
                return left % convert_int_to_const(left, right);
            },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__mod__",
            [](const int64_t &left, K &right) -> Expr & {
                return convert_int_to_const(left, right) % right;
            },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__div__", [](const K &left, const Var &right) -> Expr & { return left / right; },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__div__",
            [](const K &left, const int64_t &right) -> Expr & {
                return left / convert_int_to_const(left, right);
            },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__div__",
            [](const int64_t &left, K &right) -> Expr & {
                return convert_int_to_const(left, right) / right;
            },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__rshift__", [](const K &left, const Var &right) -> Expr & { return left >> right; },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__rshift__",
            [](const K &left, const int64_t &right) -> Expr & {
                return left >> convert_int_to_const(left, right);
            },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__rshift__",
            [](const int64_t &left, K &right) -> Expr & {
                return convert_int_to_const(left, right) >> right;
            },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__or__", [](const K &left, const Var &right) -> Expr & { return left | right; },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__or__",
            [](const K &left, const int64_t &right) -> Expr & {
                return left | convert_int_to_const(left, right);
            },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__or__",
            [](const int64_t &left, K &right) -> Expr & {
                return convert_int_to_const(left, right) | right;
            },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__and__", [](const K &left, const Var &right) -> Expr & { return left & right; },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__and__",
            [](const K &left, const int64_t &right) -> Expr & {
                return left & convert_int_to_const(left, right);
            },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__and__",
            [](const int64_t &left, K &right) -> Expr & {
                return convert_int_to_const(left, right) & right;
            },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__xor__", [](const K &left, const Var &right) -> Expr & { return left ^ right; },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__xor__",
            [](const K &left, const int64_t &right) -> Expr & {
                return left ^ convert_int_to_const(left, right);
            },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__xor__",
            [](const int64_t &left, K &right) -> Expr & {
                return convert_int_to_const(left, right) ^ right;
            },
            py::return_value_policy::reference)                     // NOLINT
        .def("ashr", &K::ashr, py::return_value_policy::reference)  // NOLINT
        .def(
            "ashr",
            [](const K &left, const int64_t &right) -> Expr & {
                return left.ashr(convert_int_to_const(left, right));
            },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "ashr",
            [](const int64_t &left, K &right) -> Expr & {
                return convert_int_to_const(left, right).ashr(right);
            },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__lt__", [](const K &left, const Var &right) -> Expr & { return left < right; },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__lt__",
            [](const K &left, const int64_t &right) -> Expr & {
                return left < convert_int_to_const(left, right);
            },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__lt__",
            [](const int64_t &left, K &right) -> Expr & {
                return convert_int_to_const(left, right) < right;
            },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__gt__", [](const K &left, const Var &right) -> Expr & { return left > right; },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__gt__",
            [](const K &left, const int64_t &right) -> Expr & {
                return left > convert_int_to_const(left, right);
            },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__gt__",
            [](const int64_t &left, K &right) -> Expr & {
                return convert_int_to_const(left, right) > right;
            },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__le__", [](const K &left, const Var &right) -> Expr & { return left <= right; },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__le__",
            [](const K &left, const int64_t &right) -> Expr & {
                return left <= convert_int_to_const(left, right);
            },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__le__",
            [](const int64_t &left, K &right) -> Expr & {
                return convert_int_to_const(left, right) <= right;
            },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__ge__", [](const K &left, const Var &right) -> Expr & { return left >= right; },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__ge__",
            [](const K &left, const int64_t &right) -> Expr & {
                return left >= convert_int_to_const(left, right);
            },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__ge__",
            [](const int64_t &left, K &right) -> Expr & {
                return convert_int_to_const(left, right) >= right;
            },
            py::return_value_policy::reference)  // NOLINT
        .def("eq", &K::eq, py::return_value_policy::reference)
        .def(
            "eq",
            [](const K &left, const int64_t &right) -> Expr & {
                return left.eq(convert_int_to_const(left, right));
            },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "eq",
            [](const int64_t &left, K &right) -> Expr & {
                return convert_int_to_const(left, right).eq(right);
            },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__neq__", [](const K &left, const Var &right) -> Expr & { return left != right; },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__neq__",
            [](const K &left, const int64_t &right) -> Expr & {
                return left != convert_int_to_const(left, right);
            },
            py::return_value_policy::reference)  // NOLINT
        .def(
            "__neq__",
            [](const int64_t &left, K &right) -> Expr & {
                return convert_int_to_const(left, right) != right;
            },
            py::return_value_policy::reference)
        .def("assign", py::overload_cast<const shared_ptr<Var> &>(&K::assign))
        .def("assign",
             [](K &left, const int64_t right) -> std::shared_ptr<AssignStmt> {
                 return left.assign(convert_int_to_const(left, right));
             })
        .def("assign", py::overload_cast<const shared_ptr<Var> &>(&K::assign))
        .def("__call__",
             [](K &left, const int64_t right) -> std::shared_ptr<AssignStmt> {
                 return left.assign(convert_int_to_const(left, right));
             })
        .def("__call__", py::overload_cast<const shared_ptr<Var> &>(&K::assign))
        .def("type", &K::type)
        .def("concat", &K::concat, py::return_value_policy::reference)
        .def_readwrite("name", &K::name)
        .def_property(
            "width", [](K &var) { return var.var_width; },
            [](K &var, uint32_t width) {
                var.var_width = width;
                if (var.size == 1) {
                    var.width = width;
                } else {
                    var.width = var.size * width;
                }
            })
        .def_readwrite("signed", &K::is_signed)
        .def("sources", &K::sources, py::return_value_policy::reference)
        .def("sinks", &K::sinks, py::return_value_policy::reference)
        .def("cast", &K::cast)
        .def_property_readonly("generator", [](const K &var) { return var.generator; });

    def_attributes<T, K>(class_);
}

#endif  // KRATOS_KRATOS_EXPR_HH
