#include <pybind11/operators.h>
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>
#include "../src/expr.hh"
#include "../src/generator.hh"
#include "../src/pass.hh"
#include "../src/stmt.hh"

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

    pass_m.def("fix_assignment_type", &fix_assignment_type);
    pass_m.def("remove_unused_vars", &remove_unused_vars);
    pass_m.def("verify_generator_connectivity", &verify_generator_connectivity);
    pass_m.def("create_module_instantiation", &create_module_instantiation);
    pass_m.def("hash_generators", &hash_generators);
    pass_m.def("decouple_generator_ports", &decouple_generator_ports);
    pass_m.def("uniquify_generators", &uniquify_generators);
    pass_m.def("uniquify_module_instances", &uniquify_module_instances);
    pass_m.def("generate_verilog", &generate_verilog);
}

template <typename T, typename K>
void init_common_expr(T &class_) {
    class_.def("__repr__", &K::to_string)
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
        .def("ashr", &K::ashr)      // NOLINT
        .def(py::self < py::self)   // NOLINT
        .def(py::self > py::self)   // NOLINT
        .def(py::self <= py::self)  // NOLINT
        .def(py::self >= py::self)  // NOLINT
        .def("eq", &K::eq);
}

template <typename T>
void init_var_base(py::class_<T, std::shared_ptr<T>> &class_) {
    init_common_expr<py::class_<T, std::shared_ptr<T>>, Var>(class_);
}

template <typename T>
void init_var_derived(py::class_<T, std::shared_ptr<T>, Var> &class_) {
    init_common_expr<py::class_<T, std::shared_ptr<T>, Var>, T>(class_);
}

// deal with all the expr/var stuff
void init_expr(py::module &m) {
    auto var = py::class_<Var, ::shared_ptr<Var>>(m, "Var");
    init_var_base(var);

    auto expr = py::class_<Expr, ::shared_ptr<Expr>, Var>(m, "Expr");
    init_var_derived(expr);

    auto port = py::class_<Port, ::shared_ptr<Port>, Var>(m, "Port");
    init_var_derived(port);

    auto const_ = py::class_<Const, ::shared_ptr<Const>, Var>(m, "Const");
    init_var_derived(const_);

    auto slice = py::class_<VarSlice, ::shared_ptr<VarSlice>, Var>(m, "VarSlice");
    init_var_derived(slice);

    auto concat = py::class_<VarConcat, ::shared_ptr<VarConcat>, Var>(m, "VarConcat");
    init_var_derived(concat);
}

void init_context(py::module &m) {
    auto context = py::class_<Context>(m, "Context");
    context.def(py::init()).def("generator", &Context::generator);
}

void init_generator(py::module &m) {
    auto generator = py::class_<Generator, ::shared_ptr<Generator>>(m, "Generator");
    generator.def("from_verilog", &Generator::from_verilog)
        .def("var", py::overload_cast<const std::string &, uint32_t>(&Generator::var))
        .def("var", py::overload_cast<const std::string &, uint32_t, bool>(&Generator::var))
        .def("port",
             py::overload_cast<PortDirection, const std::string &, uint32_t>(&Generator::port))
        .def("port",
             py::overload_cast<PortDirection, const std::string &, uint32_t, PortType, bool>(
                 &Generator::port))
        .def("constant", py::overload_cast<int64_t, uint32_t>(&Generator::constant))
        .def("constant", py::overload_cast<int64_t, uint32_t, bool>(&Generator::constant))
        .def("get_port", &Generator::get_port)
        .def("get_var", &Generator::get_var)
        .def("get_port_names", &Generator::get_port_names)
        .def("vars", &Generator::vars)
        .def("add_stmt", &Generator::add_stmt)
        .def("remove_stmt", &Generator::remove_stmt)
        .def("add_child_generator", &Generator::add_child_generator)
        .def("remove_child_generator", &Generator::remove_child_generator)
        .def("get_child_generators", &Generator::get_child_generators)
        .def("should_child_inline", &Generator::should_child_inline)
        .def("set_child_inline", &Generator::set_child_inline)
        .def("external", &Generator::external)
        .def("get_unique_variable_name", &Generator::get_unique_variable_name)
        .def("context", &Generator::context);
}

void init_stmt(py::module &m) {
    py::class_<Stmt, ::shared_ptr<Stmt>>(m, "Stmt")
        .def(py::init<StatementType>())
        .def("type", &Stmt::type);

    py::class_<AssignStmt, ::shared_ptr<AssignStmt>, Stmt>(m, "AssignStmt")
        .def("assign_type", &AssignStmt::assign_type)
        .def("set_assign_type", &AssignStmt::set_assign_type)
        .def("left", &AssignStmt::left)
        .def("right", &AssignStmt::right)
        .def("set_left", &AssignStmt::set_left)
        .def("set_right", &AssignStmt::set_right);

    py::class_<IfStmt, ::shared_ptr<IfStmt>, Stmt>(m, "IfStmt")
        .def(py::init<::shared_ptr<Var>>())
        .def("predicate", &IfStmt::predicate)
        .def("then_body", &IfStmt::then_body)
        .def("else_body", &IfStmt::else_body)
        .def("add_then_stmt", py::overload_cast<const ::shared_ptr<Stmt> &>(&IfStmt::add_then_stmt))
        .def("add_else_stmt",
             py::overload_cast<const ::shared_ptr<Stmt> &>(&IfStmt::add_else_stmt));

    py::class_<SwitchStmt, ::shared_ptr<SwitchStmt>, Stmt>(m, "SwitchStmt")
        .def(py::init<const ::shared_ptr<Var> &>())
        .def("add_switch_case", &SwitchStmt::add_switch_case)
        .def("target", &SwitchStmt::target)
        .def("body", &SwitchStmt::body);

    py::class_<CombinationalStmtBlock, ::shared_ptr<CombinationalStmtBlock>, Stmt>(
        m, "CombinationalStmtBlock")
        .def(py::init<>())
        .def("block_type", &CombinationalStmtBlock::block_type)
        .def("add_statement",
             py::overload_cast<::shared_ptr<Stmt>>(&CombinationalStmtBlock::add_statement));

    py::class_<SequentialStmtBlock, ::shared_ptr<SequentialStmtBlock>, Stmt>(m,
                                                                             "SequentialStmtBlock")
        .def(py::init<>())
        .def("get_conditions", &SequentialStmtBlock::get_conditions)
        .def("add_condition", &SequentialStmtBlock::add_condition);

    py::class_<ModuleInstantiationStmt, ::shared_ptr<ModuleInstantiationStmt>, Stmt>(
        m, "ModuleInstantiationStmt")
        .def(py::init<Generator *, Generator *>());
}

PYBIND11_MODULE(_kratos, m) {
    m.doc() = "C++ Python binding for kratos";
    init_enum(m);
    init_pass(m);
    init_expr(m);
    init_context(m);
    init_generator(m);
    init_stmt(m);
}
