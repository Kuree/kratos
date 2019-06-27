#include <pybind11/operators.h>
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>
#include "../src/expr.hh"
#include "../src/generator.hh"
#include "../src/pass.hh"
#include "../src/stmt.hh"

namespace py = pybind11;
using std::shared_ptr;

// pass submodule
void init_pass(py::module &m) {
    auto pass_m = m.def_submodule("pass");

    pass_m.def("fix_assignment_type", &fix_assignment_type);
    pass_m.def("remove_unused_vars", &remove_unused_vars);
    pass_m.def("verify_generator_connectivity", &verify_generator_connectivity);
    pass_m.def("create_module_instantiation", &create_module_instantiation);
    pass_m.def("hash_generators", &hash_generators);
    pass_m.def("decouple_generator_ports", &decouple_generator_ports);
    pass_m.def("uniquify_generators", &uniquify_generators);
    pass_m.def("uniquify_module_instances", &uniquify_module_instances);
}

template <typename T>
void init_common_expr(py::class_<T, std::shared_ptr<T>> &class_) {
    class_.def("__repr__", &T::to_string)
        .def(~py::self)
        .def(-py::self)
        .def(+py::self)
        .def(py::self + py::self)   // NOLINT
        .def(py::self - py::self)   // NOLINT
        .def(py::self * py::self)   // NOLINT
        .def(py::self % py::self)   // NOLINT
        .def(py::self / py::self)   // NOLINT
        .def(py::self >> py::self)  // NOLINT
        .def(py::self | py::self)   // NOLINT
        .def(py::self & py::self)   // NOLINT
        .def(py::self ^ py::self)   // NOLINT
        .def("ashr", &T::ashr)    // NOLINT
        .def(py::self < py::self)   // NOLINT
        .def(py::self > py::self)   // NOLINT
        .def(py::self <= py::self)  // NOLINT
        .def(py::self >= py::self)  // NOLINT
        .def("eq", &T::eq);
}

// deal with all the expr/var stuff
void init_expr(py::module &m) {
    auto var = py::class_<Var, ::shared_ptr<Var>>(m, "Var");
    init_common_expr(var);

    auto expr = py::class_<Expr, ::shared_ptr<Expr>>(m, "Expr");
    init_common_expr(expr);
}

void init_context(py::module &m) {
    auto context = py::class_<Context>(m, "Context");
    context.def(py::init())
        .def("generator", &Context::generator);
}

void init_generator(py::module &m) {
    auto generator = py::class_<Generator, ::shared_ptr<Generator>>(m, "Generator");
    generator.def("from_verilog", &Generator::from_verilog)
        .def("var", py::overload_cast<const std::string &, uint32_t>(&Generator::var))
        .def("var", py::overload_cast<const std::string &, uint32_t, bool>(&Generator::var));
}

PYBIND11_MODULE(_kratos, m) {
    m.doc() = "C++ Python binding for kratos";
    init_pass(m);
    init_expr(m);
    init_context(m);
    init_generator(m);
}