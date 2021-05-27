#include <pybind11/functional.h>
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>

#include "../src/event.hh"
#include "../src/generator.hh"

namespace py = pybind11;

void init_event(py::module &m) {
    using namespace kratos;
    py::class_<EventTracingStmtWrapper, std::shared_ptr<EventTracingStmtWrapper>, AuxiliaryStmt>(
        m, "EventTracingStmt")
        .def("terminates", &EventTracingStmtWrapper::terminates)
        .def("belongs", &EventTracingStmtWrapper::belongs)
        .def("starts", &EventTracingStmtWrapper::starts);

    m.def("extract_event_fire_condition", &extract_event_fire_condition);
}
