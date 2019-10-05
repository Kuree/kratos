#include <pybind11/functional.h>
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>
#include "../src/expr.hh"
#include "../src/stmt.hh"
#include "../src/port.hh"
#include "../src/pass.hh"


namespace py = pybind11;

// bind all the enums
void init_enum(py::module &m) {
    using namespace kratos;
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
        .value("Initial", StatementBlockType::Initial)
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
        .value("Unsigned", VarCastType::Unsigned)
        .value("AsyncReset", VarCastType::AsyncReset)
        .value("Clock", VarCastType::Clock);
}