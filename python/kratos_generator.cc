#include <pybind11/functional.h>
#include <pybind11/operators.h>
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>
#include "../src/except.hh"
#include "../src/expr.hh"
#include "../src/fsm.hh"
#include "../src/generator.hh"
#include "../src/stmt.hh"

namespace py = pybind11;
using std::shared_ptr;

void init_generator(py::module &m) {
    using namespace kratos;
    auto generator = py::class_<Generator, ::shared_ptr<Generator>, IRNode>(m, "Generator");
    generator.def("from_verilog", &Generator::from_verilog)
        .def("var", py::overload_cast<const std::string &, uint32_t>(&Generator::var),
             py::return_value_policy::reference)
        .def("var",
             py::overload_cast<const std::string &, uint32_t, uint32_t, bool>(&Generator::var),
             py::return_value_policy::reference)
        .def(
            "var",
            [](Generator &gen, const std::string &name, const std::shared_ptr<Param> &width,
               uint32_t size, bool is_signed) -> Var & {
                auto &v = gen.var(name, width->value(), size, is_signed);
                v.set_width_param(width);
                return v;
            },
            py::return_value_policy::reference)
        .def("port",
             py::overload_cast<PortDirection, const std::string &, uint32_t>(&Generator::port),
             py::return_value_policy::reference)
        .def("port",
             py::overload_cast<PortDirection, const std::string &, uint32_t, uint32_t, PortType,
                               bool>(&Generator::port),
             py::return_value_policy::reference)
        .def(
            "port",
            [](Generator &gen, PortDirection dir, const std::string &name,
               const std::shared_ptr<Param> &width, uint32_t size, PortType t,
               bool is_signed) -> Port & {
                auto &p = gen.port(dir, name, width->value(), size, t, is_signed);
                p.set_width_param(width);
                return p;
            },
            py::return_value_policy::reference)
        .def("parameter",
             py::overload_cast<const std::string &, uint32_t, bool>(&Generator::parameter),
             py::return_value_policy::reference)
        .def("port_packed", &Generator::port_packed, py::return_value_policy::reference)
        .def("enum", &Generator::enum_, py::return_value_policy::reference)
        .def("get_params", &Generator::get_params)
        .def("get_param", &Generator::get_param)
        .def("get_port", &Generator::get_port, py::return_value_policy::reference)
        .def("get_var", &Generator::get_var, py::return_value_policy::reference)
        .def("get_port_names", &Generator::get_port_names)
        .def("vars", &Generator::vars)
        .def("has_var", &Generator::has_var)
        .def("has_port", &Generator::has_port)
        .def("add_stmt", &Generator::add_stmt)
        .def("remove_port", &Generator::remove_port)
        .def("remove_var", &Generator::remove_var)
        .def("remove_stmt", &Generator::remove_stmt)
        .def("stmts_count", &Generator::stmts_count)
        .def("get_stmt", &Generator::get_stmt)
        .def("sequential", &Generator::sequential, py::return_value_policy::reference)
        .def("combinational", &Generator::combinational, py::return_value_policy::reference)
        .def("initial", &Generator::initial, py::return_value_policy::reference)
        .def("add_child_generator",
             py::overload_cast<const std::string &, const std::shared_ptr<Generator> &>(
                 &Generator::add_child_generator))
        .def("add_child_generator",
             py::overload_cast<const std::string &, const std::shared_ptr<Generator> &,
                               const std::pair<std::string, uint32_t> &>(
                 &Generator::add_child_generator))
        .def("remove_child_generator", &Generator::remove_child_generator)
        .def("get_child_generators", &Generator::get_child_generators)
        .def("has_child_generator",
             py::overload_cast<const std::shared_ptr<Generator> &>(&Generator::has_child_generator))
        .def("has_child_generator",
             py::overload_cast<const std::string &>(&Generator::has_child_generator))
        .def("get_child_generator_size", &Generator::get_child_generator_size)
        .def("external", &Generator::external)
        .def("set_external", &Generator::set_external)
        .def("external_filename", &Generator::external_filename)
        .def("is_stub", &Generator::is_stub)
        .def("set_is_stub", &Generator::set_is_stub)
        .def("wire_ports", &Generator::wire_ports)
        .def("correct_wire_direction", &Generator::correct_wire_direction)
        .def("correct_wire_direction",
             [](Generator &gen, const std::shared_ptr<Var> &var1, int64_t var2) {
                 auto &var = constant(var2, var1->width(), var1->is_signed());
                 return gen.correct_wire_direction(var1, var.shared_from_this());
             })
        .def("correct_wire_direction",
             [](Generator &gen, int64_t var1, const std::shared_ptr<Var> &var2) {
                 auto &var = constant(var1, var2->width(), var2->is_signed());
                 return gen.correct_wire_direction(var.shared_from_this(), var2);
             })
        .def("get_unique_variable_name", &Generator::get_unique_variable_name)
        .def("context", &Generator::context, py::return_value_policy::reference)
        .def_property(
            "instance_name", [](Generator &m) { return m.instance_name; },
            [](Generator &m, const std::string &name) {
                if (!m.parent() || m.parent()->ir_node_kind() != GeneratorKind) {
                    // top level instance name
                    m.instance_name = name;
                } else {
                    auto p = dynamic_cast<Generator *>(m.parent());
                    p->rename_child_generator(m.shared_from_this(), name);
                }
            })
        .def_property(
            "name", [](Generator &m) { return m.name; },
            [](Generator &m, const std::string &name) {
                m.context()->change_generator_name(&m, name);
            })
        .def_readwrite("debug", &Generator::debug)
        .def("clone", &Generator::clone)
        .def_property("is_cloned", &Generator::is_cloned, &Generator::set_is_cloned)
        .def("__contains__",
             py::overload_cast<const std::shared_ptr<Generator> &>(&Generator::has_child_generator))
        .def("add_attribute", &Generator::add_attribute)
        .def("replace", py::overload_cast<const std::string &, const std::shared_ptr<Generator> &>(
                            &Generator::replace))
        .def("replace",
             py::overload_cast<const std::string &, const std::shared_ptr<Generator> &,
                               const std::pair<std::string, uint32_t> &>(&Generator::replace))
        .def("get_ports", &Generator::get_ports)
        .def("add_bundle_port_def",
             py::overload_cast<const std::string &, const std::shared_ptr<PortBundleDefinition> &,
                               const std::pair<std::string, uint32_t> &>(
                 &Generator::add_bundle_port_def))
        .def("add_bundle_port_def",
             py::overload_cast<const std::string &, const std::shared_ptr<PortBundleDefinition> &>(
                 &Generator::add_bundle_port_def))
        .def("get_bundle_ref", &Generator::get_bundle_ref)
        .def("has_port_bundle", &Generator::has_port_bundle)
        .def("get_named_block", &Generator::get_named_block)
        .def("add_named_block", &Generator::add_named_block)
        .def("has_named_block", &Generator::has_named_block)
        .def("fsm", py::overload_cast<const std::string &>(&Generator::fsm),
             py::return_value_policy::reference)
        .def("fsm",
             py::overload_cast<const std::string &, const std::shared_ptr<Var> &,
                               const std::shared_ptr<Var> &>(&Generator::fsm),
             py::return_value_policy::reference)
        .def("call",
             py::overload_cast<const std::string &,
                               const std::map<std::string, std::shared_ptr<Var>> &>(
                 &Generator::call),
             py::return_value_policy::reference)
        .def("call",
             py::overload_cast<const std::string &,
                               const std::map<std::string, std::shared_ptr<Var>> &, bool>(
                 &Generator::call),
             py::return_value_policy::reference)
        .def("function", &Generator::function)
        .def("has_function", &Generator::has_function)
        .def("get_function", &Generator::get_function)
        .def("set_child_comment", &Generator::set_child_comment)
        .def_property("def_instance", &Generator::def_instance, &Generator::set_def_instance,
                      py::return_value_policy::reference)
        .def("dpi_function", &Generator::dpi_function, py::return_value_policy::reference)
        .def("handle_name", [](const Generator &generator) { return generator.handle_name(); })
        .def("handle_name", [](const Generator &generator,
                               bool ignore_top) { return generator.handle_name(ignore_top); })
        .def("parent_generator", &Generator::parent_generator);

    generator.def("add_fn_ln", [](Generator &var, const std::pair<std::string, uint32_t> &info) {
        var.fn_name_ln.emplace_back(info);
    });

    auto bundle_def = py::class_<PortBundleDefinition, std::shared_ptr<PortBundleDefinition>>(
        m, "PortBundleDefinition");
    bundle_def.def(py::init<std::string>())
        .def("add_definition", &PortBundleDefinition::add_definition)
        .def("definition", &PortBundleDefinition::definition)
        .def("flip", &PortBundleDefinition::flip)
        .def("add_debug_info", &PortBundleDefinition::add_debug_info)
        .def_property("name", &PortBundleDefinition::get_name, &PortBundleDefinition::set_name);

    auto bundle_ref = py::class_<PortBundleRef, std::shared_ptr<PortBundleRef>>(m, "PortBundleRef");
    bundle_ref
        .def(
            "__getitem__", [](PortBundleRef & ref, const std::string &name) -> auto & {
                return ref.get_port(name);
            },
            py::return_value_policy::reference)
        .def(
            "__getattr__", [](PortBundleRef & ref, const std::string &name) -> auto & {
                return ref.get_port(name);
            },
            py::return_value_policy::reference)
        .def("member_names", &PortBundleRef::member_names);
}