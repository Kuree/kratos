#ifndef KRATOS_KRATOS_DEBUG_HH
#define KRATOS_KRATOS_DEBUG_HH

#include <pybind11/pybind11.h>

#include "kratos_expr.hh"

template <typename T, typename K>
void def_trace(T &class_) {
    class_.def("add_fn_ln", [](K &var, const std::pair<std::string, uint32_t> &info) {
      var.fn_name_ln.emplace_back(info);
    });
}

template <typename T>
void init_var_base(pybind11::class_<T, std::shared_ptr<T>> &class_) {
    init_common_expr<pybind11::class_<T, std::shared_ptr<T>>, kratos::Var>(class_);
}

template <typename T>
void init_var_derived(pybind11::class_<T, std::shared_ptr<T>, kratos::Var> &class_) {
    init_common_expr<pybind11::class_<T, std::shared_ptr<T>, kratos::Var>, T>(class_);
    class_.def(
        "assign",
        [](const std::shared_ptr<T> &var_to, const std::shared_ptr<kratos::Var> &var_from,
           kratos::AssignmentType type) -> auto { return var_to->assign(var_from, type); },
        pybind11::return_value_policy::reference);
}

#endif  // KRATOS_KRATOS_DEBUG_HH
