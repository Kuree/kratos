#include <pybind11/operators.h>
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>
#include "../src/codegen.h"
#include "../src/expr.hh"
#include "../src/generator.hh"
#include "../src/pass.hh"
#include "../src/stmt.hh"
#include "../src/util.hh"

namespace py = pybind11;
using std::shared_ptr;

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
        .def("uniquify_module_instances", &uniquify_module_instances)
        .def("generate_verilog", &generate_verilog)
        .def("transform_if_to_case", &transform_if_to_case)
        .def("remove_fanout_one_wires", &remove_fanout_one_wires)
        .def("remove_pass_through_modules", &remove_pass_through_modules);
}

// util submodule
void init_util(py::module &m) {
    auto util_m = m.def_submodule("util");

    util_m.def("is_valid_verilog", &is_valid_verilog);
}

template <typename T, typename K>
void def_trace(T &class_) {
    class_.def_readwrite("fn_name_ln", &K::fn_name_ln);
}

template <typename T, typename K>
void init_common_expr(T &class_) {
    // see how available object overloads here: https://docs.python.org/3/reference/datamodel.html
    class_.def("__repr__", &K::to_string)
        .def("__invert__", [](const K &var) -> Expr & { return ~var; },
             py::return_value_policy::reference)
        .def("__neg__", [](const K &var) -> Expr & { return -var; },
             py::return_value_policy::reference)
        .def("__pos__", [](const K &var) -> Expr & { return +var; },
             py::return_value_policy::reference)
        .def("__add__", [](const K &left, const Var &right) -> Expr & { return left + right; },
             py::return_value_policy::reference)  // NOLINT
        .def("__sub__", [](const K &left, const Var &right) -> Expr & { return left - right; },
             py::return_value_policy::reference)  // NOLINT
        .def("__mul__", [](const K &left, const Var &right) -> Expr & { return left * right; },
             py::return_value_policy::reference)  // NOLINT
        .def("__mod__", [](const K &left, const Var &right) -> Expr & { return left % right; },
             py::return_value_policy::reference)  // NOLINT
        .def("__div__", [](const K &left, const Var &right) -> Expr & { return left / right; },
             py::return_value_policy::reference)  // NOLINT
        .def("__rshift__", [](const K &left, const Var &right) -> Expr & { return left >> right; },
             py::return_value_policy::reference)  // NOLINT
        .def("__or__", [](const K &left, const Var &right) -> Expr & { return left | right; },
             py::return_value_policy::reference)  // NOLINT
        .def("__and__", [](const K &left, const Var &right) -> Expr & { return left & right; },
             py::return_value_policy::reference)  // NOLINT
        .def("__xor__", [](const K &left, const Var &right) -> Expr & { return left ^ right; },
             py::return_value_policy::reference)                    // NOLINT
        .def("ashr", &K::ashr, py::return_value_policy::reference)  // NOLINT
        .def("__lt__", [](const K &left, const Var &right) -> Expr & { return left < right; },
             py::return_value_policy::reference)  // NOLINT
        .def("__gt__", [](const K &left, const Var &right) -> Expr & { return left > right; },
             py::return_value_policy::reference)  // NOLINT
        .def("__le__", [](const K &left, const Var &right) -> Expr & { return left <= right; },
             py::return_value_policy::reference)  // NOLINT
        .def("__ge__", [](const K &left, const Var &right) -> Expr & { return left >= right; },
             py::return_value_policy::reference)  // NOLINT
        .def("eq", &K::eq, py::return_value_policy::reference)
        .def("__neq__", [](const K &left, const Var &right) -> Expr & { return left != right; },
             py::return_value_policy::reference)  // NOLINT
        .def("__getitem__", [](K & k, std::pair<uint32_t, uint32_t> v) -> auto & { return k[v]; },
             py::return_value_policy::reference)
        .def("__getitem__", [](K & k, uint32_t idx) -> auto & { return k[idx]; },
             py::return_value_policy::reference)
        .def("assign", py::overload_cast<const ::shared_ptr<Var> &>(&K::assign),
             py::return_value_policy::reference)
        .def("type", &K::type)
        .def("concat", &K::concat, py::return_value_policy::reference)
        .def_readwrite("name", &K::name)
        .def_readwrite("width", &K::width)
        .def_readwrite("signed", &K::is_signed)
        .def("sources", &K::sources, py::return_value_policy::reference)
        .def("sinks", &K::sinks, py::return_value_policy::reference)
        .def("signed_", &K::signed_)
        .def_property_readonly("generator", [](const K &var) { return var.generator; });
}

template <typename T>
void init_var_base(py::class_<T, std::shared_ptr<T>> &class_) {
    init_common_expr<py::class_<T, std::shared_ptr<T>>, Var>(class_);
}

template <typename T>
void init_var_derived(py::class_<T, std::shared_ptr<T>, Var> &class_) {
    init_common_expr<py::class_<T, std::shared_ptr<T>, Var>, T>(class_);
    class_.def("assign",
               [](const std::shared_ptr<Var> var_to, const std::shared_ptr<T> var_from,
                  AssignmentType type) -> auto & { return var_to->assign(var_from, type); },
               py::return_value_policy::reference);
}

// deal with all the expr/var stuff
void init_expr(py::module &m) {
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
}

void init_context(py::module &m) {
    auto context = py::class_<Context>(m, "Context");
    context.def(py::init())
        .def("generator", &Context::generator, py::return_value_policy::reference)
        .def("clear", &Context::clear)
        .def("get_hash", &Context::get_hash)
        .def("get_generators_by_name", &Context::get_generators_by_name)
        .def("hash_table_size", &Context::hash_table_size)
        .def("change_generator_name", &Context::change_generator_name)
        .def("add", &Context::add)
        .def("has_hash", &Context::has_hash);
}

void init_generator(py::module &m) {
    auto generator = py::class_<Generator, ::shared_ptr<Generator>>(m, "Generator");
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
        .def("constant", py::overload_cast<int64_t, uint32_t>(&Generator::constant),
             py::return_value_policy::reference)
        .def("constant", py::overload_cast<int64_t, uint32_t, bool>(&Generator::constant),
             py::return_value_policy::reference)
        .def("get_port", &Generator::get_port, py::return_value_policy::reference)
        .def("get_var", &Generator::get_var, py::return_value_policy::reference)
        .def("get_port_names", &Generator::get_port_names)
        .def("vars", &Generator::vars)
        .def("add_stmt", &Generator::add_stmt)
        .def("remove_stmt", &Generator::remove_stmt)
        .def("sequential", &Generator::sequential, py::return_value_policy::reference)
        .def("combinational", &Generator::combinational, py::return_value_policy::reference)
        .def("add_child_generator", &Generator::add_child_generator,
             py::return_value_policy::reference)
        .def("remove_child_generator", &Generator::remove_child_generator)
        .def("get_child_generators", &Generator::get_child_generators)
        .def("should_child_inline", &Generator::should_child_inline)
        .def("has_child_generator", &Generator::has_child_generator)
        .def("get_child_generator_size", &Generator::get_child_generator_size)
        .def("set_child_inline", &Generator::set_child_inline)
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
        .def_readwrite("debug", &Generator::debug);

    def_trace<py::class_<Generator, ::shared_ptr<Generator>>, Generator>(generator);
}

void init_stmt(py::module &m) {
    py::class_<Stmt, ::shared_ptr<Stmt>> stmt_(m, "Stmt");
    stmt_.def(py::init<StatementType>()).def("type", &Stmt::type);
    def_trace<py::class_<Stmt, ::shared_ptr<Stmt>>, Stmt>(stmt_);

    py::class_<AssignStmt, ::shared_ptr<AssignStmt>, Stmt>(m, "AssignStmt")
        .def("assign_type", &AssignStmt::assign_type)
        .def("set_assign_type", &AssignStmt::set_assign_type)
        .def("set_left", &AssignStmt::set_left)
        .def("set_right", &AssignStmt::set_right)
        .def_property_readonly("left", [](const AssignStmt &stmt) { return stmt.left(); })
        .def_property_readonly("right", [](const AssignStmt &stmt) { return stmt.right(); });

    py::class_<IfStmt, ::shared_ptr<IfStmt>, Stmt>(m, "IfStmt")
        .def(py::init<::shared_ptr<Var>>())
        .def("predicate", &IfStmt::predicate, py::return_value_policy::reference)
        .def("then_body", &IfStmt::then_body)
        .def("else_body", &IfStmt::else_body)
        .def("add_then_stmt", py::overload_cast<const ::shared_ptr<Stmt> &>(&IfStmt::add_then_stmt))
        .def("add_else_stmt",
             py::overload_cast<const ::shared_ptr<Stmt> &>(&IfStmt::add_else_stmt));

    py::class_<SwitchStmt, ::shared_ptr<SwitchStmt>, Stmt>(m, "SwitchStmt")
        .def(py::init<const ::shared_ptr<Var> &>())
        .def("add_switch_case",
             py::overload_cast<const std::shared_ptr<Const> &, const std::shared_ptr<Stmt> &>(
                 &SwitchStmt::add_switch_case))
        .def("add_switch_case", py::overload_cast<const std::shared_ptr<Const> &,
                                                  const std::vector<std::shared_ptr<Stmt>> &>(
                                    &SwitchStmt::add_switch_case))
        .def("target", &SwitchStmt::target, py::return_value_policy::reference)
        .def("body", &SwitchStmt::body);

    py::class_<CombinationalStmtBlock, ::shared_ptr<CombinationalStmtBlock>, Stmt>(
        m, "CombinationalStmtBlock")
        .def(py::init<>())
        .def("block_type", &CombinationalStmtBlock::block_type)
        .def("add_statement",
             py::overload_cast<const ::shared_ptr<Stmt> &>(&CombinationalStmtBlock::add_statement));

    py::class_<SequentialStmtBlock, ::shared_ptr<SequentialStmtBlock>, Stmt>(m,
                                                                             "SequentialStmtBlock")
        .def(py::init<>())
        .def("get_conditions", &SequentialStmtBlock::get_conditions)
        .def("add_condition", &SequentialStmtBlock::add_condition)
        .def("add_statement",
             py::overload_cast<const ::shared_ptr<Stmt> &>(&SequentialStmtBlock::add_statement));

    py::class_<ModuleInstantiationStmt, ::shared_ptr<ModuleInstantiationStmt>, Stmt>(
        m, "ModuleInstantiationStmt")
        .def(py::init<Generator *, Generator *>());
}

void init_code_gen(py::module &m) {
    py::class_<VerilogModule>(m, "VerilogModule")
        .def(py::init<Generator *>())
        .def("verilog_src", &VerilogModule::verilog_src)
        .def("run_passes", &VerilogModule::run_passes)
        .def("debug_info", &VerilogModule::debug_info);
}

PYBIND11_MODULE(_kratos, m) {
    m.doc() = "C++ Python binding for kratos";
    init_enum(m);
    init_pass(m);
    init_expr(m);
    init_context(m);
    init_generator(m);
    init_stmt(m);
    init_code_gen(m);
    init_util(m);
}
