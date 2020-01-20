#include <pybind11/functional.h>
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>

#include "../src/fault.hh"
#include "../src/stmt.hh"

namespace py = pybind11;

void init_fault(py::module &main_m) {
    using namespace kratos;
    auto m = main_m.def_submodule("fault");
    auto run = py::class_<SimulationRun, std::shared_ptr<SimulationRun>>(m, "SimulationRun");
    run.def(py::init<Generator *>())
        .def("add_simulation_state", &SimulationRun::add_simulation_state)
        .def("mark_wrong_value", &SimulationRun::mark_wrong_value)
        .def_property_readonly("has_wrong_value", &SimulationRun::has_wrong_value)
        .def("get_state", &SimulationRun::get_state, py::return_value_policy::reference)
        .def_property_readonly("num_states", &SimulationRun::num_states);

    auto fault = py::class_<FaultAnalyzer>(m, "FaultAnalyzer");
    fault.def(py::init<Generator*>())
    .def("add_simulation_run", &FaultAnalyzer::add_simulation_run)
    .def_property_readonly("num_runs", &FaultAnalyzer::num_runs)
    .def("compute_coverage", &FaultAnalyzer::compute_coverage)
    .def("compute_fault_stmts_from_coverage", &FaultAnalyzer::compute_fault_stmts_from_coverage);

    // helper functions
    m.def("parse_verilator_coverage", &parse_verilator_coverage);
}