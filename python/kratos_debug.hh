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

#endif  // KRATOS_KRATOS_DEBUG_HH
