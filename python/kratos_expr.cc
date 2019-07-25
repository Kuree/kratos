#include "kratos_expr.hh"

namespace py = pybind11;
using std::shared_ptr;
using namespace kratos;

// deal with all the expr/var stuff
void init_expr(pybind11::module &m) {
    auto var = py::class_<Var, ::shared_ptr<Var>>(m, "Var");
    init_var_base(var);
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

    // struct info for packed
    auto struct_ = py::class_<PackedStruct>(m, "PackedStruct");
    struct_.def(py::init<std::string, std::vector<std::tuple<std::string, uint32_t, bool>>>())
        .def_readonly("struct_name", &PackedStruct::struct_name)
        .def_readonly("attributes", &PackedStruct::attributes);

    auto port_slice =
        py::class_<PortPackedSlice, ::shared_ptr<PortPackedSlice>, Var>(m, "PortPackedSlice");
    init_var_derived(port_slice);
    def_trace<py::class_<PortPackedSlice, ::shared_ptr<PortPackedSlice>, Var>, VarSlice>(
        port_slice);

    auto array = py::class_<Array, ::shared_ptr<Array>, Var>(m, "Array");
    init_var_derived(array);
    def_trace<py::class_<Array, ::shared_ptr<Array>, Var>, Var>(array);
    array.def("size", &Array::size);
}
