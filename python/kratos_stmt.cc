#include <pybind11/functional.h>
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>

#include "../src/event.hh"
#include "../src/except.hh"
#include "../src/generator.hh"
#include "kratos_debug.hh"

namespace py = pybind11;
using std::shared_ptr;

std::optional<std::pair<std::string, uint32_t>> get_fn_ln(uint32_t num_frame_back);

void add_function_call_var(kratos::StmtBlock &block,
                           const std::shared_ptr<kratos::FunctionCallVar> &var) {
    // need to convert it into a function call statement
    // SystemVerilog doesn't like a function call that returns stuff and don't
    // have an assignment associated with it
    auto *def = var->func();
    if (def != nullptr && def->has_return_value()) {
        throw kratos::UserException("Cannot discard function call that returns a variable: " +
                                    def->function_name());
    }
    auto st = std::make_shared<kratos::FunctionCallStmt>(var);
    block.add_stmt(st);
}

void init_stmt(py::module &m) {
    using namespace kratos;
    py::class_<Stmt, ::shared_ptr<Stmt>> stmt_(m, "Stmt");
    stmt_.def(py::init<StatementType>())
        .def("type", &Stmt::type)
        .def("add_scope_variable", &Stmt::add_scope_variable)
        .def("add_scope_variable",
             [](Stmt &stmt, const std::string &name, const std::string &value, bool is_var) {
                 stmt.add_scope_variable(name, value, is_var, false);
             })
        .def_property_readonly("scope_context", [](Stmt &stmt) { return stmt.scope_context(); })
        .def("set_parent", &Stmt::set_parent)
        .def("clone", &Stmt::clone);

    def_trace<py::class_<Stmt, ::shared_ptr<Stmt>>, Stmt>(stmt_);
    def_attributes<py::class_<Stmt, ::shared_ptr<Stmt>>, Stmt>(stmt_);

    py::class_<AssignStmt, ::shared_ptr<AssignStmt>, Stmt> assign_(
        m, "AssignStmt", R"pbdoc(Assignment statement)pbdoc");
    assign_.def("assign_type", &AssignStmt::assign_type)
        .def("set_assign_type", &AssignStmt::set_assign_type)
        .def_property_readonly(
            "left", [](const AssignStmt &stmt) { return stmt.left(); },
            py::return_value_policy::reference)
        .def_property_readonly(
            "right", [](const AssignStmt &stmt) { return stmt.right(); },
            py::return_value_policy::reference)
        .def_property("delay", &AssignStmt::get_delay, &AssignStmt::set_delay)
        .def_property_readonly("has_delay", &AssignStmt::has_delay);

    py::class_<IfStmt, ::shared_ptr<IfStmt>, Stmt>(m, "IfStmt")
        .def(py::init<::shared_ptr<Var>>())
        .def("predicate", &IfStmt::predicate, py::return_value_policy::reference)
        .def("then_body", &IfStmt::then_body)
        .def_property_readonly("then_", &IfStmt::then_body)
        .def_property_readonly("else_", &IfStmt::else_body)
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
        .def("add_stmt", &add_function_call_var)
        .def("__getitem__",
             [](StmtBlock &stmt, int index) {
                 if (stmt.empty()) {
                     throw UserException("Index of out range");
                 }
                 while (index < 0) {
                     index += stmt.size();
                 }
                 return stmt.get_stmt(index);
             })
        .def("__setitem__",
             [](StmtBlock &stmt, int index, const std::shared_ptr<Stmt> &value) {
                 if (stmt.empty()) {
                     throw UserException("Index of out range");
                 }
                 while (index < 0) {
                     index += stmt.size();
                 }
                 stmt.set_child(index, value);
             })
        .def("__len__", [](StmtBlock &stmt) { return stmt.size(); })
        .def(
            "__iter__", [](StmtBlock &stmt) { return py::make_iterator(stmt.begin(), stmt.end()); },
            py::keep_alive<0, 1>());

    py::class_<CombinationalStmtBlock, ::shared_ptr<CombinationalStmtBlock>, StmtBlock>(
        m, "CombinationalStmtBlock")
        .def(py::init<>())
        .def_property("general_purpose", &CombinationalStmtBlock::is_general_purpose,
                      &CombinationalStmtBlock::set_general_purpose);

    py::class_<LatchStmtBlock, ::shared_ptr<LatchStmtBlock>, StmtBlock>(m, "LatchStmtBlock")
        .def(py::init<>());

    py::class_<ScopedStmtBlock, ::shared_ptr<ScopedStmtBlock>, StmtBlock>(m, "ScopedStmtBlock")
        .def(py::init<>());

    py::class_<SequentialStmtBlock, ::shared_ptr<SequentialStmtBlock>, StmtBlock>(
        m, "SequentialStmtBlock")
        .def(py::init<>())
        .def("get_event_controls", py::overload_cast<>(&SequentialStmtBlock::get_event_controls))
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

    py::class_<BuiltInFunctionStmtBlock, std::shared_ptr<BuiltInFunctionStmtBlock>,
               FunctionStmtBlock>(m, "BuiltInFunctionStmtBlock")
        .def("return_width", &BuiltInFunctionStmtBlock::return_width);

    py::class_<InitialStmtBlock, std::shared_ptr<InitialStmtBlock>, StmtBlock>(m,  // NOLINT
                                                                               "InitialStmtBlock");

    py::class_<FinalStmtBlock, std::shared_ptr<FinalStmtBlock>, StmtBlock>(m,  // NOLINT
                                                                           "FinalStmtBlock");

    py::class_<CommentStmt, std::shared_ptr<CommentStmt>, Stmt>(m, "CommentStmt")
        .def(py::init<const std::string>());
    // help function
    m.def("comment", [](const std::string &comment) {
         auto stmt = std::make_shared<CommentStmt>(comment);
         return stmt;
     }).def("comment", [](const std::string &comment, uint32_t line_width) {
        auto stmt = std::make_shared<CommentStmt>(comment, line_width);
        return stmt;
    });

    py::class_<RawStringStmt, std::shared_ptr<RawStringStmt>, Stmt>(m, "RawStringStmt")
        .def(py::init<const std::string &>())
        .def(py::init<const std::vector<std::string> &>());

    py::class_<ForStmt, std::shared_ptr<ForStmt>, Stmt>(m, "ForStmt")
        .def(py::init<const std::string &, int64_t, int64_t, int64_t>())
        .def("get_iter_var", &ForStmt::get_iter_var)
        .def("add_stmt", &ForStmt::add_stmt)
        .def("add_stmt",
             [](ForStmt &for_, const std::shared_ptr<FunctionCallVar> &var) {
                 add_function_call_var(*for_.get_loop_body(), var);
             })
        .def("get_loop_body", &ForStmt::get_loop_body);

    py::class_<BreakStmt, std::shared_ptr<BreakStmt>, Stmt>(m, "BreakStmt").def(py::init<>());

    py::class_<AuxiliaryStmt, std::shared_ptr<AuxiliaryStmt>, Stmt>(m, "AuxiliaryStmt")
        .def("aux", &AuxiliaryStmt::aux_type);

    py::class_<EventTracingStmt, std::shared_ptr<EventTracingStmt>, AuxiliaryStmt>(
        m, "EventTracingStmt")
        .def("terminates", py::overload_cast<>(&EventTracingStmt::terminates))
        .def("terminates", py::overload_cast<const std::string &>(&EventTracingStmt::terminates))
        .def("belongs", &EventTracingStmt::belongs)
        .def("belongs",
             [](EventTracingStmt &stmt, const Transaction &t) { return stmt.belongs(t.name); })
        .def("belongs",
             [](EventTracingStmt &stmt, const Transaction &t, const std::string &filename,
                uint64_t ln) {
                 auto s = stmt.belongs(t.name);
                 s->fn_name_ln.emplace_back(std::make_pair(filename, ln));
                 return s;
             })
        .def("starts", py::overload_cast<>(&EventTracingStmt::starts))
        .def("starts", py::overload_cast<const std::string &>(&EventTracingStmt::starts))
        .def("matches", &EventTracingStmt::matches)
        .def("matches",
             [](std::shared_ptr<EventTracingStmt> &stmt, const py::kwargs &kwargs) {
                 for (auto const &[n, v] : kwargs) {
                     auto name = py::cast<std::string>(n);
                     auto var = py::cast<std::shared_ptr<Var>>(v);
                     stmt->matches(name, var);
                 }
                 return stmt;
             })
        .def_property_readonly("match_values", &EventTracingStmt::match_values);

    py::class_<EventDelayStmt, std::shared_ptr<EventDelayStmt>, AuxiliaryStmt>(m, "EventDelayStmt")
        .def_property_readonly("event", &EventDelayStmt::event)
        .def(py::init<EventControl>());

    // event control
    py::class_<EventControl>(m, "EventControl")
        .def(py::init<uint64_t>())
        .def(py::init<EventEdgeType, Var &>())
        .def_readwrite("delay_side", &EventControl::delay_side)
        .def_readwrite("delay", &EventControl::delay)
        .def_readwrite("edge", &EventControl::edge);
}
