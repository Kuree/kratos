#include <pybind11/functional.h>
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>
#include "../src/except.hh"
#include "../src/expr.hh"
#include "../src/generator.hh"
#include "../src/stmt.hh"
#include "kratos_debug.hh"

namespace py = pybind11;
using std::shared_ptr;

void init_stmt(py::module &m) {
    using namespace kratos;
    py::class_<Stmt, ::shared_ptr<Stmt>> stmt_(m, "Stmt");
    stmt_.def(py::init<StatementType>()).def("type", &Stmt::type);
    def_trace<py::class_<Stmt, ::shared_ptr<Stmt>>, Stmt>(stmt_);

    py::class_<AssignStmt, ::shared_ptr<AssignStmt>, Stmt> assign_(
        m, "AssignStmt", R"pbdoc(Assignment statement)pbdoc");
    assign_.def("assign_type", &AssignStmt::assign_type)
        .def("set_assign_type", &AssignStmt::set_assign_type)
        .def_property_readonly("left", [](const AssignStmt &stmt) { return stmt.left(); })
        .def_property_readonly("right", [](const AssignStmt &stmt) { return stmt.right(); });

    def_attributes<py::class_<AssignStmt, ::shared_ptr<AssignStmt>, Stmt>, AssignStmt>(assign_);

    py::class_<IfStmt, ::shared_ptr<IfStmt>, Stmt>(m, "IfStmt")
        .def(py::init<::shared_ptr<Var>>())
        .def("predicate", &IfStmt::predicate, py::return_value_policy::reference)
        .def("then_body", &IfStmt::then_body)
        .def("else_body", &IfStmt::else_body)
        .def("add_then_stmt", py::overload_cast<const ::shared_ptr<Stmt> &>(&IfStmt::add_then_stmt))
        .def("add_else_stmt", py::overload_cast<const ::shared_ptr<Stmt> &>(&IfStmt::add_else_stmt))
        .def("remove_then_stmt",
             py::overload_cast<const ::shared_ptr<Stmt> &>(&IfStmt::remove_then_stmt))
        .def("remove_else_stmt",
             py::overload_cast<const ::shared_ptr<Stmt> &>(&IfStmt::remove_else_stmt));

    py::class_<SwitchStmt, ::shared_ptr<SwitchStmt>, Stmt>(m, "SwitchStmt")
        .def(py::init<const ::shared_ptr<Var> &>())
        .def("add_switch_case",
             py::overload_cast<const std::shared_ptr<Const> &, const std::shared_ptr<Stmt> &>(
                 &SwitchStmt::add_switch_case))
        .def("add_switch_case", py::overload_cast<const std::shared_ptr<Const> &,
                                                  const std::vector<std::shared_ptr<Stmt>> &>(
                                    &SwitchStmt::add_switch_case))
        .def("target", &SwitchStmt::target, py::return_value_policy::reference)
        .def("body", &SwitchStmt::body)
        .def("remove_switch_case", py::overload_cast<const std::shared_ptr<kratos::Const> &>(
                                       &SwitchStmt::remove_switch_case))
        .def("remove_switch_case",
             py::overload_cast<const std::shared_ptr<Const> &, const std::shared_ptr<Stmt> &>(
                 &SwitchStmt::remove_switch_case));

    py::class_<CombinationalStmtBlock, ::shared_ptr<CombinationalStmtBlock>, Stmt>(
        m, "CombinationalStmtBlock")
        .def(py::init<>())
        .def("block_type", &CombinationalStmtBlock::block_type)
        .def("add_stmt",
             py::overload_cast<const ::shared_ptr<Stmt> &>(&CombinationalStmtBlock::add_stmt))
        .def("remove_stmt", &CombinationalStmtBlock::remove_stmt);

    py::class_<StmtBlock, ::shared_ptr<StmtBlock>, Stmt>(m, "StmtBlock");  // NOLINT

    py::class_<ScopedStmtBlock, ::shared_ptr<ScopedStmtBlock>, StmtBlock>(m, "ScopedStmtBlock")
        .def(py::init<>())
        .def("add_stmt", py::overload_cast<const ::shared_ptr<Stmt> &>(&ScopedStmtBlock::add_stmt));

    py::class_<SequentialStmtBlock, ::shared_ptr<SequentialStmtBlock>, StmtBlock>(
        m, "SequentialStmtBlock")
        .def(py::init<>())
        .def("get_conditions", &SequentialStmtBlock::get_conditions)
        .def("add_condition", &SequentialStmtBlock::add_condition)
        .def("add_stmt",
             py::overload_cast<const ::shared_ptr<Stmt> &>(&SequentialStmtBlock::add_stmt))
        .def("remove_stmt", &SequentialStmtBlock::remove_stmt);

    py::class_<ModuleInstantiationStmt, ::shared_ptr<ModuleInstantiationStmt>, Stmt>(
        m, "ModuleInstantiationStmt")
        .def(py::init<Generator *, Generator *>());

    py::class_<ReturnStmt, std::shared_ptr<ReturnStmt>, Stmt>(m, "ReturnStmt");
    py::class_<FunctionStmtBlock, std::shared_ptr<FunctionStmtBlock>, StmtBlock>(
        m, "FunctionStmtBlock")
        .def("input", &FunctionStmtBlock::input)
        .def("return_stmt", &FunctionStmtBlock::return_stmt)
        .def("add_stmt",
             py::overload_cast<const ::shared_ptr<Stmt> &>(&FunctionStmtBlock::add_stmt))
        .def("get_port", &FunctionStmtBlock::get_port);
}