#include <pybind11/functional.h>
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>

#include "../src/expr.hh"
#include "../src/pass.hh"
#include "../src/port.hh"
#include "../src/stmt.hh"
#include "../src/tb.hh"

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
        .value("Latch", StatementBlockType::Latch)
        .value("Final", StatementBlockType::Final)
        .export_values();

    py::enum_<EventEdgeType>(m, "EventEdgeType")
        .value("Posedge", EventEdgeType::Posedge)
        .value("Negedge", EventEdgeType::Negedge)
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
        .value("ClockEnable", VarCastType::ClockEnable)
        .value("Clock", VarCastType::Clock)
        .value("Enum", VarCastType::Enum)
        .value("Resize", VarCastType::Resize);

    py::enum_<PropertyAction>(m, "PropertyAction")
        .value("None", PropertyAction::None)
        .value("Cover", PropertyAction::Cover)
        .value("Assume", PropertyAction::Assume)
        .value("Assert", PropertyAction::Assert);

    py::enum_<ParamType>(m, "ParamType")
        .value("RawType", ParamType::RawType)
        .value("Parameter", ParamType::Parameter)
        .value("Enum", ParamType::Enum)
        .value("Integral", ParamType::Integral);

    py::enum_<AuxiliaryType>(m, "AuxiliaryType").value("Event", AuxiliaryType::EventTracing);

    py::enum_<EventActionType>(m, "EventActionType")
        .value("None_", EventActionType::None)
        .value("Start", EventActionType::Start)
        .value("End", EventActionType::End);

    py::enum_<EventControl::DelaySide>(m, "DelaySide")
        .value("Left", EventControl::DelaySide::left)
        .value("Right", EventControl::DelaySide::right);
}