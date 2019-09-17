#include <pybind11/functional.h>
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>
#include "../src/except.hh"
#include "../src/expr.hh"
#include "../src/generator.hh"
#include "../src/pass.hh"
#include "../src/stmt.hh"
#include "../src/debug.hh"

#include "kratos_expr.hh"

namespace py = pybind11;
using std::shared_ptr;
using namespace kratos;

// pass submodule
void init_pass(py::module &m) {
    auto pass_m = m.def_submodule("passes");

    pass_m.def("fix_assignment_type", &fix_assignment_type)
        .def("remove_unused_vars", &remove_unused_vars)
        .def("verify_generator_connectivity", &verify_generator_connectivity)
        .def("create_module_instantiation", &create_module_instantiation)
        .def("hash_generators", &hash_generators)
        .def("hash_generators_parallel", &hash_generators_parallel)
        .def("hash_generators_sequential", &hash_generators_sequential)
        .def("decouple_generator_ports", &decouple_generator_ports)
        .def("uniquify_generators", &uniquify_generators)
        .def("generate_verilog", py::overload_cast<Generator *>(&generate_verilog))
        .def("generate_verilog",
             py::overload_cast<Generator *, const std::string &, const std::string &, bool>(
                 &generate_verilog))
        .def("transform_if_to_case", &transform_if_to_case)
        .def("remove_fanout_one_wires", &remove_fanout_one_wires)
        .def("remove_pass_through_modules", &remove_pass_through_modules)
        .def("extract_debug_info", &extract_debug_info)
        .def("extract_struct_info", &extract_struct_info)
        .def("merge_wire_assignments", merge_wire_assignments)
        .def("zero_out_stubs", &zero_out_stubs)
        .def("remove_unused_stmts", &remove_unused_stmts)
        .def("check_mixed_assignment", &check_mixed_assignment)
        .def("zero_generator_inputs", &zero_generator_inputs)
        .def("insert_pipeline_stages", &insert_pipeline_stages)
        .def("change_port_bundle_struct", &change_port_bundle_struct)
        .def("realize_fsm", &realize_fsm)
        .def("check_function_return", &check_function_return)
        .def("sort_stmts", &sort_stmts)
        .def("check_active_high", &check_active_high)
        .def("extract_dpi_function", &extract_dpi_function)
        .def("extract_debug_break_points", &extract_debug_break_points)
        .def("insert_verilator_public", &insert_verilator_public)
        .def("check_inferred_latch", &check_inferred_latch);

    auto manager = py::class_<PassManager>(pass_m, "PassManager", R"pbdoc(
This class gives you the fined control over which pass to run and in which order.
Most passes doesn't return anything, thus it's safe to put it in the pass manager and
let is run. However, if you want to code gen verilog, you have to call generate_verilog()
by yourself to obtain the verilog code.)pbdoc");
    manager.def(py::init<>())
        .def("register_pass",
             py::overload_cast<const std::string &, std::function<void(Generator *)>>(
                 &PassManager::register_pass))
        .def("run_passes", &PassManager::run_passes)
        .def("add_pass", &PassManager::add_pass)
        .def("has_pass", &PassManager::has_pass);

    // trampoline class for ast visitor
    class PyIRVisitor : public IRVisitor {
    public:
        using IRVisitor::IRVisitor;

        void visit_root(IRNode *root) override {
            PYBIND11_OVERLOAD(void, IRVisitor, visit_root, root);
        }

        void visit_generator_root(Generator *generator) override {
            PYBIND11_OVERLOAD(void, IRVisitor, visit_generator_root, generator);
        }

        void visit_content(Generator *generator) override {
            PYBIND11_OVERLOAD(void, IRVisitor, visit_content, generator);
        }

        void visit(AssignStmt *stmt) override { PYBIND11_OVERLOAD(void, IRVisitor, visit, stmt); }

        void visit(Port *var) override { PYBIND11_OVERLOAD(void, IRVisitor, visit, var); }

        void visit(Generator *generator) override {
            PYBIND11_OVERLOAD(void, IRVisitor, visit, generator);
        }
    };

    auto ast_visitor = py::class_<IRVisitor, PyIRVisitor>(pass_m, "IRVisitor");
    ast_visitor.def(py::init<>())
        .def("visit_generator", py::overload_cast<Generator *>(&IRVisitor::visit))
        .def("visit_root", &IRVisitor::visit_root);

    auto ast = py::class_<IRNode, std::shared_ptr<IRNode>>(pass_m, "IRNode");
    ast.def(py::init<IRNodeKind>());
    def_attributes<py::class_<IRNode, std::shared_ptr<IRNode>>, IRNode>(ast);

    // attributes
    // type holder due to conversion
    class PyAttribute : public Attribute {
    private:
        explicit PyAttribute(py::object target) : Attribute(), target_(std::move(target)) {
            type_str = "python";
        }

    public:
        using Attribute::Attribute;

        py::object get_py_obj() { return target_; }

        static PyAttribute create(const py::object &target) { return PyAttribute(target); }

    private:
        py::object target_ = py::none();
    };

    auto attribute =
        py::class_<Attribute, PyAttribute, std::shared_ptr<Attribute>>(pass_m, "Attribute");
    attribute.def(py::init(&PyAttribute::create))
        .def_readwrite("type_str", &PyAttribute::type_str)
        .def("get", [=](PyAttribute &attr) { return attr.get_py_obj(); })
        .def_readwrite("value_str", &PyAttribute::value_str);
    py::implicitly_convertible<Attribute, PyAttribute>();
}