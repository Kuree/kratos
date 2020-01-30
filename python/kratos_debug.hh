#ifndef KRATOS_KRATOS_DEBUG_HH
#define KRATOS_KRATOS_DEBUG_HH

#include <pybind11/pybind11.h>

#include "kratos_expr.hh"

template <typename T, typename K>
void def_trace(T &class_) {
    class_.def("add_fn_ln", [](K &var, const std::pair<std::string, uint32_t> &info) {
      var.fn_name_ln.emplace_back(info);
    })
    .def("add_fn_ln", [](K &var, const std::pair<std::string, uint32_t> &info, bool insert_front) {
        if (insert_front) {
            var.fn_name_ln.insert(var.fn_name_ln.begin(), info);
        } else {
            var.fn_name_ln.emplace_back(info);
        }
    })
    .def_readwrite("comment", &K::comment)
    .def_readwrite("fn_name_ln", &K::fn_name_ln)
    .def_property_readonly("verilog_ln", [](K& k) { return k.verilog_ln; });
}

#endif  // KRATOS_KRATOS_DEBUG_HH
