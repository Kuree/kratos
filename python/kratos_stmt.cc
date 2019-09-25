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
    stmt_.def(py::init<StatementType>())
        .def("type", &Stmt::type)
        .def("add_scope_variable", &Stmt::add_scope_variable)
        .def("add_scope_variable",
             [](Stmt &stmt, const std::string &name, const std::string &value, bool is_var) {
                 stmt.add_scope_variable(name, value, is_var, false);
             });

    def_trace<py::class_<Stmt, ::shared_ptr<Stmt>>, Stmt>(stmt_);

    py::class_<AssignStmt, ::shared_ptr<AssignStmt>, Stmt> assign_(
        m, "AssignStmt", R"pbdoc(Assignment statement)pbdoc");
    assign_.def("assign_type", &AssignStmt::assign_type)
        .def("set_assign_type", &AssignStmt::set_assign_type)
        .def_property_readonly("left", [](const AssignStmt &stmt) { return stmt.left(); })
        .def_property_readonly("right", [](const AssignStmt &stmt) { return stmt.right(); })
        .def_property("delay", &AssignStmt::get_delay, &AssignStmt::set_delay);

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

    py::class_<StmtBlock, ::shared_ptr<StmtBlock>, Stmt>(m, "StmtBlock")
        .def("block_type", &StmtBlock::block_type)
        .def("add_stmt", py::overload_cast<const ::shared_ptr<Stmt> &>(&StmtBlock::add_stmt))
        .def("remove_stmt", &StmtBlock::remove_stmt)
        .def("add_stmt", [](StmtBlock &stmt, const std::shared_ptr<FunctionCallVar> &var) {
            // need to convert it into a function call statement
            auto st = std::make_shared<FunctionCallStmt>(var);
            stmt.add_stmt(st);
        });

    py::class_<CombinationalStmtBlock, ::shared_ptr<CombinationalStmtBlock>, StmtBlock>(
        m, "CombinationalStmtBlock")
        .def(py::init<>());

    py::class_<ScopedStmtBlock, ::shared_ptr<ScopedStmtBlock>, StmtBlock>(m, "ScopedStmtBlock")
        .def(py::init<>());

    py::class_<SequentialStmtBlock, ::shared_ptr<SequentialStmtBlock>, StmtBlock>(
        m, "SequentialStmtBlock")
        .def(py::init<>())
        .def("get_conditions", &SequentialStmtBlock::get_conditions)
        .def("add_condition", &SequentialStmtBlock::add_condition);

    py::class_<ModuleInstantiationStmt, ::shared_ptr<ModuleInstantiationStmt>, Stmt>(
        m, "ModuleInstantiationStmt")
        .def(py::init<Generator *, Generator *>());

    py::class_<ReturnStmt, std::shared_ptr<ReturnStmt>, Stmt>(m, "ReturnStmt");  // NOLINT
    py::class_<FunctionStmtBlock, std::shared_ptr<FunctionStmtBlock>, StmtBlock>(
        m, "FunctionStmtBlock")
        .def("input", &FunctionStmtBlock::input)
        .def("return_stmt", &FunctionStmtBlock::return_stmt)
        .def("get_port", &FunctionStmtBlock::get_port)
        .def("set_port_ordering", py::overload_cast<const std::map<std::string, uint32_t> &>(
                                      &FunctionStmtBlock::set_port_ordering))
        .def("set_port_ordering", py::overload_cast<const std::map<uint32_t, std::string> &>(
                                      &FunctionStmtBlock::set_port_ordering));
    py::class_<DPIFunctionStmtBlock, std::shared_ptr<DPIFunctionStmtBlock>, FunctionStmtBlock>(
        m, "DPIFunctionStmtBlock")
        .def("input", &DPIFunctionStmtBlock::input)
        .def("output", &DPIFunctionStmtBlock::output)
        .def("set_return_width", &DPIFunctionStmtBlock::set_return_width)
        .def("is_pure", &DPIFunctionStmtBlock::is_pure)
        .def("is_context", &DPIFunctionStmtBlock::is_context)
        .def("set_is_pure", &DPIFunctionStmtBlock::set_is_pure)
        .def("set_is_context", &DPIFunctionStmtBlock::set_is_context);

    py::class_<InitialStmtBlock, std::shared_ptr<InitialStmtBlock>, StmtBlock>(m,
                                                                               "InitialStmtBlock");
}
