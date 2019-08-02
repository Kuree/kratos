#include "kratos_expr.hh"
#include <pybind11/functional.h>
#include <pybind11/stl.h>
#include "kratos_debug.hh"

namespace py = pybind11;
using std::shared_ptr;

// deal with all the expr/var stuff
void init_expr(py::module &m) {
    using namespace kratos;
    auto var = py::class_<Var, ::shared_ptr<Var>>(m, "Var");
    init_var_base(var);
    init_getitem<py::class_<Var, ::shared_ptr<Var>>, Var>(var);
    def_trace<py::class_<Var, ::shared_ptr<Var>>, Var>(var);

    auto expr = py::class_<Expr, ::shared_ptr<Expr>, Var>(m, "Expr");
    init_var_derived(expr);
    def_trace<py::class_<Expr, ::shared_ptr<Expr>, Var>, Expr>(expr);

    auto port = py::class_<Port, ::shared_ptr<Port>, Var>(m, "Port");
    init_var_derived(port);
    port.def("port_direction", &Port::port_direction).def("port_type", &Port::port_type);
    def_trace<py::class_<Port, ::shared_ptr<Port>, Var>, Port>(port);

    auto const_ = py::class_<Const, ::shared_ptr<Const>, Var>(m, "Const");
    init_var_derived(const_);
    const_.def("value", &Const::value).def("set_value", &Const::set_value);
    def_trace<py::class_<Const, ::shared_ptr<Const>, Var>, Const>(const_);

    auto slice = py::class_<VarSlice, ::shared_ptr<VarSlice>, Var>(m, "VarSlice");
    init_var_derived(slice);
    def_trace<py::class_<VarSlice, ::shared_ptr<VarSlice>, Var>, VarSlice>(slice);

    auto concat = py::class_<VarConcat, ::shared_ptr<VarConcat>, Var>(m, "VarConcat");
    init_var_derived(concat);
    def_trace<py::class_<VarConcat, ::shared_ptr<VarConcat>, Var>, VarConcat>(concat);

    auto param = py::class_<Param, ::shared_ptr<Param>, Var>(m, "Param");
    init_var_derived(param);
    param.def("value", &Param::value).def("set_value", &Param::set_value);
    def_trace<py::class_<Param, ::shared_ptr<Param>, Var>, Param>(param);

    auto port_packed = py::class_<PortPacked, ::shared_ptr<PortPacked>, Var>(m, "PortPacked");
    init_var_derived(port_packed);
    port_packed.def("port_direction", &PortPacked::port_direction)
        .def("port_type", &PortPacked::port_type)
        .def(
            "__getitem__",
            [](PortPacked & port, const std::string &name) -> auto & { return port[name]; },
            py::return_value_policy::reference);
    def_trace<py::class_<PortPacked, ::shared_ptr<PortPacked>, Var>, PortPacked>(port_packed);

    auto var_packed = py::class_<VarPacked, ::shared_ptr<VarPacked>, Var>(m, "VarPacked");
    init_var_derived(var_packed);
    var_packed
        .def(
            "__getitem__",
            [](VarPacked & port, const std::string &name) -> auto & { return port[name]; },
            py::return_value_policy::reference);
    def_trace<py::class_<VarPacked, ::shared_ptr<VarPacked>, Var>, VarPacked>(var_packed);

    // struct info for packed
    auto struct_ = py::class_<PackedStruct>(m, "PackedStruct");
    struct_.def(py::init<std::string, std::vector<std::tuple<std::string, uint32_t, bool>>>())
        .def_readonly("struct_name", &PackedStruct::struct_name)
        .def_readonly("attributes", &PackedStruct::attributes);

    auto port_packed_slice =
        py::class_<PackedSlice, ::shared_ptr<PackedSlice>, Var>(m, "PackedSlice");
    init_var_derived(port_packed_slice);
    def_trace<py::class_<PackedSlice, ::shared_ptr<PackedSlice>, Var>, VarSlice>(
        port_packed_slice);

    // ternary op
    auto ternary_exp =
        py::class_<ConditionalExpr, ::shared_ptr<ConditionalExpr>, Expr>(m, "ConditionalExpr");
    ternary_exp.def(py::init<const std::shared_ptr<Var> &, const std::shared_ptr<Var> &,
                             const std::shared_ptr<Var> &>());
}

void init_enum_type(py::module &m) {
    using namespace kratos;
    auto enum_ = py::class_<Enum>(m, "Enum");
    enum_.def_readonly("name", &Enum::name);
}