#include <pybind11/functional.h>
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>

#include "../src/except.hh"
#include "../src/interface.hh"

namespace py = pybind11;

// interface submodule
void init_interface(py::module &m) {
    using namespace kratos;
    auto interface =
        py::class_<InterfaceDefinition, std::shared_ptr<InterfaceDefinition>>(m, "Interface");
    interface.def(py::init<const std::string &>())
        .def("input", &InterfaceDefinition::input)
        .def("output", &InterfaceDefinition::output)
        .def("var",
             py::overload_cast<const std::string &, uint32_t, uint32_t>(&InterfaceDefinition::var))
        .def("var", py::overload_cast<const std::string &, uint32_t, const std::vector<uint32_t> &>(
                        &InterfaceDefinition::var))
        .def("var", py::overload_cast<const std::string &, uint32_t>(&InterfaceDefinition::var))
        .def("port", py::overload_cast<const std::string &, uint32_t, uint32_t, PortDirection>(
                         &InterfaceDefinition::port))
        .def("port", py::overload_cast<const std::string &, uint32_t, const std::vector<uint32_t> &,
                                       PortDirection>(&InterfaceDefinition::port))
        .def("port", py::overload_cast<const std::string &, uint32_t, const std::vector<uint32_t> &,
                                       PortDirection, PortType>(&InterfaceDefinition::port))
        .def("clock", &InterfaceDefinition::clock)
        .def("reset", &InterfaceDefinition::reset)
        .def("modport", &InterfaceDefinition::create_modport_def)
        .def("has_var", &InterfaceDefinition::has_var)
        .def("has_port", &InterfaceDefinition::has_port)
        .def("__contains__", [](InterfaceDefinition &def, const std::string &name) {
            return def.has_port(name) || def.has_var(name);
        });

    auto modport_interface =
        py::class_<InterfaceModPortDefinition, std::shared_ptr<InterfaceModPortDefinition>>(
            m, "ModPortInterface");
    modport_interface.def("set_input", &InterfaceModPortDefinition::set_input)
        .def("set_output", &InterfaceModPortDefinition::set_output);

    auto ref = py::class_<InterfaceRef, std::shared_ptr<InterfaceRef>>(m, "InterfaceRef");
    ref.def(
           "var", [](InterfaceRef &ref, const std::string &name) -> Var & { return ref.var(name); },
           py::return_value_policy::reference)
        .def(
            "port",
            [](InterfaceRef &ref, const std::string &name) -> Port & { return ref.port(name); },
            py::return_value_policy::reference)
        .def("has_var", &InterfaceRef::has_var)
        .def("has_port", &InterfaceRef::has_port)
        .def("__contains__",
             [](InterfaceRef &ref, const std::string &name) {
                 return ref.has_port(name) || ref.has_var(name);
             })
        .def(
            "__getitem__",
            [](InterfaceRef &ref, const std::string &name) -> Var * {
                if (ref.has_port(name)) {
                    return &ref.port(name);
                } else if (ref.has_var(name)) {
                    return &ref.var(name);
                } else {
                    throw UserException(name + " not exist in " + ref.name());
                }
            },
            py::return_value_policy::reference)
        .def(
            "__getattr__",
            [](InterfaceRef &ref, const std::string &name) -> Var * {
                if (ref.has_port(name)) {
                    return &ref.port(name);
                } else if (ref.has_var(name)) {
                    return &ref.var(name);
                } else if (name == "__len__") {
                    return nullptr;
                } else {
                    throw UserException(name + " not exist in " + ref.name());
                }
            },
            py::return_value_policy::reference)
        .def("has_modport", &InterfaceRef::has_modport)
        .def("get_modport_ref", &InterfaceRef::get_modport_ref);
}