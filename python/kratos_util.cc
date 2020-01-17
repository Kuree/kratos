#include <pybind11/functional.h>
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>
#include "../src/util.hh"
#include "../src/except.hh"

namespace py = pybind11;
using std::shared_ptr;
using namespace kratos;

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
        .def("get_num_cpus", &get_num_cpus)
        .def("print_stmts", [](const std::vector<std::shared_ptr<Stmt>> &stmts) {
            for (auto const &stmt: stmts)
                print_ast_node(stmt.get());
        })
        .def("print_stmts", [](const std::set<std::shared_ptr<Stmt>> &stmts) {
          for (auto const &stmt: stmts)
              print_ast_node(stmt.get());
        });
}