#include "../src/codegen.hh"
#include "../src/except.hh"
#include "../src/expr.hh"
#include "../src/generator.hh"
#include "../src/pass.hh"
#include "../src/stmt.hh"
#include "../src/util.hh"

#include "kratos_expr.hh"
#include "kratos_stmt.hh"

namespace py = pybind11;
using std::shared_ptr;
using namespace kratos;

// bind all the enums
void init_enum(py::module &m) {
    py::enum_<PortType>(m, "PortType")
        .value("Clock", PortType::Clock)
        .value("AsyncReset", PortType::AsyncReset)
        .value("ClockEnable", PortType::ClockEnable)
        .value("Data", PortType::Data)
        .value("Reset", PortType::Reset)
        .export_values();

    py::enum_<PortDirection>(m, "PortDirection")
        .value("In", PortDirection::In)
        .value("Out", PortDirection::Out)
        .value("InOut", PortDirection::InOut)
        .export_values();

    py::enum_<HashStrategy>(m, "HashStrategy")
        .value("SequentialHash", HashStrategy::SequentialHash)
        .value("ParallelHash", HashStrategy::ParallelHash)
        .export_values();

    py::enum_<StatementType>(m, "StatementType")
        .value("If", StatementType::If)
        .value("Switch", StatementType::Switch)
        .value("Assign", StatementType::Assign)
        .value("Block", StatementType::Block)
        .value("ModuleInstantiation", StatementType::ModuleInstantiation)
        .export_values();

    py::enum_<AssignmentType>(m, "AssignmentType")
        .value("Blocking", AssignmentType::Blocking)
        .value("NonBlocking", AssignmentType::NonBlocking)
        .value("Undefined", AssignmentType::Undefined)
        .export_values();

    py::enum_<StatementBlockType>(m, "StatementBlockType")
        .value("Combinational", StatementBlockType::Combinational)
        .value("Sequential", StatementBlockType::Sequential)
        .export_values();

    py::enum_<BlockEdgeType>(m, "BlockEdgeType")
        .value("Posedge", BlockEdgeType::Posedge)
        .value("Negedge", BlockEdgeType::Negedge)
        .export_values();

    py::enum_<IRNodeKind>(m, "IRNodeKind")
        .value("GeneratorKind", IRNodeKind::GeneratorKind)
        .value("VarKind", IRNodeKind::VarKind)
        .value("StmtKind", IRNodeKind::StmtKind)
        .export_values();

    py::enum_<VarCastType>(m, "VarCastType")
        .value("Signed", VarCastType::Signed)
        .value("AsyncReset", VarCastType::AsyncReset)
        .value("Clock", VarCastType::Clock);
}

// pass submodule
void init_pass(py::module &m) {
    auto pass_m = m.def_submodule("passes");

    pass_m.def("fix_assignment_type", &fix_assignment_type)
        .def("remove_unused_vars", &remove_unused_vars)
        .def("verify_generator_connectivity", &verify_generator_connectivity)
        .def("create_module_instantiation", &create_module_instantiation)
        .def("hash_generators", &hash_generators)
        .def("decouple_generator_ports", &decouple_generator_ports)
        .def("uniquify_generators", &uniquify_generators)
        .def("generate_verilog", &generate_verilog)
        .def("transform_if_to_case", &transform_if_to_case)
        .def("remove_fanout_one_wires", &remove_fanout_one_wires)
        .def("remove_pass_through_modules", &remove_pass_through_modules)
        .def("extract_debug_info", &extract_debug_info)
        .def("extract_struct_info", &extract_struct_info)
        .def("merge_wire_assignments", merge_wire_assignments)
        .def("zero_out_stubs", &zero_out_stubs)
        .def("remove_unused_vars", &remove_unused_vars)
        .def("check_mixed_assignment", &check_mixed_assignment);

    auto manager = py::class_<PassManager>(pass_m, "PassManager", R"pbdoc(
This class gives you the fined control over which pass to run and in which order.
Most passes doesn't return anything, thus it's safe to put it in the pass manager and
let is run. However, if you want to code gen verilog, you have to call generate_verilog()
by yourself to obtain the verilog code.)pbdoc");
    manager.def(py::init<>())
        .def("add_pass", py::overload_cast<const std::string &, std::function<void(Generator *)>>(
                             &PassManager::add_pass))
        .def("run_passes", &PassManager::run_passes)
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
        .def_readwrite("_value_str", &PyAttribute::value_str);
    py::implicitly_convertible<Attribute, PyAttribute>();
}

// exception module
void init_except(py::module &m) {
    auto except_m = m.def_submodule("exception");
    py::register_exception<VarException>(except_m, "VarException");
    py::register_exception<StmtException>(except_m, "StmtException");
}

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
             "have to have either verilator or iverilog in your $PATH to use this function");
}

void init_context(py::module &m) {
    auto context = py::class_<Context>(m, "Context");
    context.def(py::init())
        .def("generator", &Context::generator, py::return_value_policy::reference)
        .def("empty_generator", &Context::empty_generator)
        .def("clear", &Context::clear)
        .def("get_hash", &Context::get_hash)
        .def("get_generators_by_name", &Context::get_generators_by_name)
        .def("hash_table_size", &Context::hash_table_size)
        .def("change_generator_name", &Context::change_generator_name)
        .def("add", &Context::add)
        .def("has_hash", &Context::has_hash);
}

void init_generator(py::module &m) {
    auto generator = py::class_<Generator, ::shared_ptr<Generator>, IRNode>(m, "Generator");
    generator.def("from_verilog", &Generator::from_verilog)
        .def("var", py::overload_cast<const std::string &, uint32_t>(&Generator::var),
             py::return_value_policy::reference)
        .def("var", py::overload_cast<const std::string &, uint32_t, bool>(&Generator::var),
             py::return_value_policy::reference)
        .def("port",
             py::overload_cast<PortDirection, const std::string &, uint32_t>(&Generator::port),
             py::return_value_policy::reference)
        .def("port",
             py::overload_cast<PortDirection, const std::string &, uint32_t, PortType, bool>(
                 &Generator::port),
             py::return_value_policy::reference)
        .def("array",
             py::overload_cast<const std::string &, uint32_t, uint32_t, bool>(&Generator::array),
             py::return_value_policy::reference)
        .def("array", py::overload_cast<const std::string &, uint32_t, uint32_t>(&Generator::array),
             py::return_value_policy::reference)
        .def("constant", py::overload_cast<int64_t, uint32_t>(&Generator::constant),
             py::return_value_policy::reference)
        .def("constant", py::overload_cast<int64_t, uint32_t, bool>(&Generator::constant),
             py::return_value_policy::reference)
        .def("parameter",
             py::overload_cast<const std::string &, uint32_t, bool>(&Generator::parameter),
             py::return_value_policy::reference)
        .def("port_packed", &Generator::port_packed, py::return_value_policy::reference)
        .def("get_params", &Generator::get_params)
        .def("get_param", &Generator::get_param)
        .def("get_port", &Generator::get_port, py::return_value_policy::reference)
        .def("get_var", &Generator::get_var, py::return_value_policy::reference)
        .def("get_port_names", &Generator::get_port_names)
        .def("vars", &Generator::vars)
        .def("add_stmt", &Generator::add_stmt)
        .def("remove_stmt", &Generator::remove_stmt)
        .def("stmts_count", &Generator::stmts_count)
        .def("get_stmt", &Generator::get_stmt)
        .def("sequential", &Generator::sequential, py::return_value_policy::reference)
        .def("combinational", &Generator::combinational, py::return_value_policy::reference)
        .def("add_child_generator",
             py::overload_cast<const std::string &, const std::shared_ptr<Generator> &>(
                 &Generator::add_child_generator))
        .def("add_child_generator",
             py::overload_cast<const std::string &, const std::shared_ptr<Generator> &,
                               const std::pair<std::string, uint32_t> &>(
                 &Generator::add_child_generator))
        .def("remove_child_generator", &Generator::remove_child_generator)
        .def("get_child_generators", &Generator::get_child_generators)
        .def("get_child_generator_size", &Generator::get_child_generator_size)
        .def("replace_child_generator", &Generator::replace_child_generator)
        .def("external", &Generator::external)
        .def("set_external", &Generator::set_external)
        .def("external_filename", &Generator::external_filename)
        .def("is_stub", &Generator::is_stub)
        .def("set_is_stub", &Generator::set_is_stub)
        .def("wire_ports", &Generator::wire_ports)
        .def("get_unique_variable_name", &Generator::get_unique_variable_name)
        .def("context", &Generator::context, py::return_value_policy::reference)
        .def_readwrite("instance_name", &Generator::instance_name)
        .def_readwrite("name", &Generator::name)
        .def_readwrite("debug", &Generator::debug)
        .def("clone", &Generator::clone)
        .def_property("is_cloned", &Generator::is_cloned, &Generator::set_is_cloned)
        .def("__contains__", &Generator::has_child_generator);

    generator.def("add_fn_ln", [](Generator &var, const std::pair<std::string, uint32_t> &info) {
        var.fn_name_ln.emplace_back(info);
    });
}



void init_code_gen(py::module &m) {
    py::class_<VerilogModule>(m, "VerilogModule")
        .def(py::init<Generator *>())
        .def("verilog_src", &VerilogModule::verilog_src)
        .def("run_passes", &VerilogModule::run_passes)
        .def("debug_info", &VerilogModule::debug_info)
        .def("pass_manager", &VerilogModule::pass_manager, py::return_value_policy::reference);
}

PYBIND11_MODULE(_kratos, m) {
    m.doc() = R"pbdoc(
        .. currentmodule:: _kratos
    )pbdoc";

    init_enum(m);
    init_pass(m);
    init_expr(m);
    init_context(m);
    init_generator(m);
    init_stmt(m);
    init_code_gen(m);
    init_util(m);
    init_except(m);
}
