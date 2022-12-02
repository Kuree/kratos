#include <pybind11/functional.h>
#include <pybind11/operators.h>
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>

#include "../src/except.hh"
#include "../src/expr.hh"
#include "../src/fsm.hh"
#include "../src/generator.hh"
#include "../src/interface.hh"
#include "../src/stmt.hh"
#include "../src/tb.hh"

namespace py = pybind11;
using std::shared_ptr;

void init_generator(py::module &m) {
    using namespace kratos;
    auto generator = py::class_<Generator, ::shared_ptr<Generator>, IRNode>(m, "Generator");
    generator.def("from_verilog", &Generator::from_verilog, py::return_value_policy::reference)
        .def("var", py::overload_cast<const std::string &, uint32_t>(&Generator::var),
             py::return_value_policy::reference)
        .def("var",
             py::overload_cast<const std::string &, uint32_t, uint32_t, bool>(&Generator::var),
             py::return_value_policy::reference)
        .def("var",
             py::overload_cast<const std::string &, uint32_t, const std::vector<uint32_t> &>(
                 &Generator::var),
             py::return_value_policy::reference)
        .def("var",
             py::overload_cast<const std::string &, uint32_t, const std::vector<uint32_t> &, bool>(
                 &Generator::var),
             py::return_value_policy::reference)
        .def(
            "var",
            [](Generator &gen, const std::string &name, const std::shared_ptr<Var> &width,
               uint32_t size, bool is_signed) -> Var & {
                auto &v = gen.var(name, 1, size, is_signed);
                v.set_width_param(width);
                return v;
            },
            py::return_value_policy::reference)
        .def(
            "var",
            [](Generator &gen, const std::string &name, const std::shared_ptr<Var> &width,
               const std::vector<uint32_t> &size, bool is_signed) -> Var & {
                auto &v = gen.var(name, 1, size, is_signed);
                v.set_width_param(width);
                return v;
            },
            py::return_value_policy::reference)
        .def("var", py::overload_cast<const Var &, const std::string &>(&Generator::var),
             py::return_value_policy::reference)
        .def("port",
             py::overload_cast<PortDirection, const std::string &, uint32_t>(&Generator::port),
             py::return_value_policy::reference)
        .def("port",
             py::overload_cast<PortDirection, const std::string &, uint32_t, uint32_t, PortType,
                               bool>(&Generator::port),
             py::return_value_policy::reference)
        .def("port",
             py::overload_cast<PortDirection, const std::string &, uint32_t,
                               const std::vector<uint32_t> &, PortType, bool>(&Generator::port),
             py::return_value_policy::reference)
        .def(
            "port",
            [](Generator &gen, PortDirection dir, const std::string &name,
               const std::shared_ptr<Var> &width, uint32_t size, PortType t,
               bool is_signed) -> Port & {
                auto &p = gen.port(dir, name, 1, size, t, is_signed);
                p.set_width_param(width);
                return p;
            },
            py::return_value_policy::reference)
        .def(
            "port",
            [](Generator &gen, PortDirection dir, const std::string &name,
               const std::shared_ptr<Var> &width, const std::vector<uint32_t> &size, PortType t,
               bool is_signed) -> Port & {
                auto &p = gen.port(dir, name, 1, size, t, is_signed);
                p.set_width_param(width);
                return p;
            },
            py::return_value_policy::reference)
        .def("port",
             py::overload_cast<PortDirection, const std::string &, const std::shared_ptr<Enum> &>(
                 &Generator::port),
             py::return_value_policy::reference)
        .def("port", py::overload_cast<const EnumPort &, bool>(&Generator::port),
             py::return_value_policy::reference)
        .def("port",
             py::overload_cast<const EnumPort &, const std::string &, bool>(&Generator::port),
             py::return_value_policy::reference)
        .def(
            "port", [](Generator & gen, const Port &p) -> auto & { return gen.port(p, true); },
            py::return_value_policy::reference)
        .def(
            "port", [](Generator & gen, const Port &p, const std::string &name) -> auto & {
                return gen.port(p, name, true);
            },
            py::return_value_policy::reference)
        .def(
            "port",
            [](Generator & gen, const Port &p, const std::string &name,
               bool check_param) -> auto & { return gen.port(p, name, check_param); },
            py::return_value_policy::reference)
        .def("port", py::overload_cast<const Port &, bool>(&Generator::port),
             py::return_value_policy::reference)
        .def("port", py::overload_cast<const Port &, const std::string &, bool>(&Generator::port),
             py::return_value_policy::reference)
        .def("port", py::overload_cast<const PortPackedStruct &, bool>(&Generator::port),
             py::return_value_policy::reference)
        .def("port",
             py::overload_cast<const PortPackedStruct &, const std::string &, bool>(
                 &Generator::port),
             py::return_value_policy::reference)
        .def("parameter", py::overload_cast<const std::string &>(&Generator::parameter),
             py::return_value_policy::reference)
        .def("parameter",
             py::overload_cast<const std::string &, uint32_t, bool>(&Generator::parameter),
             py::return_value_policy::reference)
        .def(
            "parameter",
            [](Generator & generator, const std::shared_ptr<Param> &param,
               std::optional<std::string> param_name) -> auto & {
                auto name = param_name ? param_name.value() : param->parameter_name();
                return generator.parameter(param, name);
            },
            py::return_value_policy::reference)
        .def("parameter",
             py::overload_cast<const std::string &, const std::shared_ptr<Enum> &>(
                 &Generator::parameter),
             py::return_value_policy::reference)
        .def("interface", [](Generator &generator, const std::shared_ptr<InterfaceDefinition> &def,
                             const std::string &name,
                             bool is_port) { return generator.interface(def, name, is_port); })
        .def("interface",
             [](Generator &generator, const std::shared_ptr<InterfaceModPortDefinition> &def,
                const std::string &name,
                bool is_port) { return generator.interface(def, name, is_port); })
        .def("has_interface",
             [](Generator &gen, const std::string &name) {
                 auto const &interfaces = gen.interfaces();
                 return interfaces.find(name) != interfaces.end();
             })
        .def("get_interface",
             [](Generator &gen, const std::string &name) -> std::shared_ptr<InterfaceRef> {
                 auto const &interfaces = gen.interfaces();
                 if (name == "__len__") return nullptr;
                 if (interfaces.find(name) == interfaces.end())
                     throw UserException(name + " doesn't exist in " + gen.handle_name() +
                                         " as interface");
                 return interfaces.at(name);
             })
        .def("port_packed",
             py::overload_cast<PortDirection, const std::string &,
                               const std::shared_ptr<PackedStruct> &>(&Generator::port_packed),
             py::return_value_policy::reference)
        .def("port_packed",
             py::overload_cast<PortDirection, const std::string &,
                               const std::shared_ptr<PackedStruct> &, uint32_t>(
                 &Generator::port_packed),
             py::return_value_policy::reference)
        .def(
            "port_packed",
            py::overload_cast<PortDirection, const std::string &,
                              const std::shared_ptr<PackedStruct> &, const std::vector<uint32_t> &>(
                &Generator::port_packed),
            py::return_value_policy::reference)
        .def("var_packed",
             py::overload_cast<const std::string &, const std::shared_ptr<PackedStruct> &>(
                 &Generator::var_packed),
             py::return_value_policy::reference)
        .def(
            "var_packed",
            py::overload_cast<const std::string &, const std::shared_ptr<PackedStruct> &, uint32_t>(
                &Generator::var_packed),
            py::return_value_policy::reference)
        .def("var_packed",
             py::overload_cast<const std::string &, const std::shared_ptr<PackedStruct> &,
                               const std::vector<uint32_t> &>(&Generator::var_packed),
             py::return_value_policy::reference)
        .def("enum", &Generator::enum_, py::return_value_policy::reference)
        .def("enum_var", &Generator::enum_var, py::return_value_policy::reference)
        .def("get_params", &Generator::get_params)
        .def("get_param", &Generator::get_param)
        .def("get_port", &Generator::get_port, py::return_value_policy::reference)
        .def("get_var", &Generator::get_var, py::return_value_policy::reference)
        .def("get_port_names", &Generator::get_port_names)
        .def("vars", &Generator::vars)
        .def("has_var", &Generator::has_var)
        .def("has_port", &Generator::has_port)
        .def("add_stmt", &Generator::add_stmt)
        .def("property", &Generator::property)
        .def("remove_port", &Generator::remove_port)
        .def("remove_var", &Generator::remove_var)
        .def("remove_stmt", &Generator::remove_stmt)
        .def("stmts_count", &Generator::stmts_count)
        .def("get_stmt", &Generator::get_stmt)
        .def("sequential", &Generator::sequential, py::return_value_policy::reference)
        .def("combinational", &Generator::combinational, py::return_value_policy::reference)
        .def("initial", &Generator::initial, py::return_value_policy::reference)
        .def("final", &Generator::final, py::return_value_policy::reference)
        .def("latch", &Generator::latch, py::return_value_policy::reference)
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
        .def("set_lib_files", &Generator::set_lib_files)
        .def("is_stub", &Generator::is_stub)
        .def("set_is_stub", &Generator::set_is_stub)
        .def("wire_ports", &Generator::wire_ports)
        .def("wire", &Generator::wire)
        .def("unwire", &Generator::unwire)
        .def("wire_interface", &Generator::wire_interface)
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
        .def("set_clone_ref", &Generator::set_clone_ref)
        .def_property("is_cloned", &Generator::is_cloned, &Generator::set_is_cloned)
        .def("copy_over_missing_ports", &Generator::copy_over_missing_ports)
        .def("__contains__",
             py::overload_cast<const std::shared_ptr<Generator> &>(&Generator::has_child_generator))
        .def("add_attribute", &Generator::add_attribute)
        .def("add_attribute",
             [](Generator &generator, const std::string &value) {
                 auto attr = std::make_shared<Attribute>();
                 attr->value_str = value;
                 generator.add_attribute(attr);
             })
        .def("replace", py::overload_cast<const std::string &, const std::shared_ptr<Generator> &>(
                            &Generator::replace))
        .def("replace",
             py::overload_cast<const std::string &, const std::shared_ptr<Generator> &,
                               const std::pair<std::string, uint32_t> &>(&Generator::replace))
        .def("get_ports", &Generator::get_ports)
        .def("add_bundle_port_def",
             py::overload_cast<const std::string &, const PortBundleDefinition &,
                               const std::pair<std::string, uint32_t> &>(
                 &Generator::add_bundle_port_def))
        .def("add_bundle_port_def",
             py::overload_cast<const std::string &, const PortBundleDefinition &>(
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
        .def("call",
             py::overload_cast<const std::string &, const std::vector<std::shared_ptr<Var>> &>(
                 &Generator::call),
             py::return_value_policy::reference)
        .def("function", &Generator::function)
        .def("task", &Generator::task)
        .def("has_function", &Generator::has_function)
        .def("get_function", &Generator::get_function)
        .def("set_child_comment", &Generator::set_child_comment)
        .def_property("def_instance", &Generator::def_instance, &Generator::set_def_instance,
                      py::return_value_policy::reference)
        .def("dpi_function", &Generator::dpi_function, py::return_value_policy::reference)
        .def("builtin_function", &Generator::builtin_function, py::return_value_policy::reference)
        .def("handle_name", [](const Generator &generator) { return generator.handle_name(); })
        .def("handle_name", [](const Generator &generator,
                               bool ignore_top) { return generator.handle_name(ignore_top); })
        .def("ports_iter",
             [](const Generator &generator) {
                 return py::make_iterator(generator.get_port_names());
             })
        .def("vars_iter",
             [](const Generator &generator) { return py::make_iterator(generator.vars()); })
        .def(
            "param_iter",
            [](const Generator &generator) { return py::make_iterator(generator.get_params()); },
            py::return_value_policy::reference)
        .def("add_raw_import", &Generator::add_raw_import)
        .def_property_readonly("raw_package_imports", &Generator::raw_package_imports)
        .def("parent_generator",
             [](const Generator &generator) { return generator.parent_generator(); })
        .def_readwrite("verilog_fn", &Generator::verilog_fn);

    generator
        .def("add_fn_ln",
             [](Generator &var, const std::pair<std::string, uint32_t> &info) {
                 var.fn_name_ln.emplace_back(info);
             })
        .def_property_readonly("verilog_ln", [](Generator &gen) { return gen.verilog_ln; });

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
        .def("member_names", &PortBundleRef::member_names)
        .def("assign", &PortBundleRef::assign);
}
