#include "kratos_expr.hh"
#include <pybind11/functional.h>
#include <pybind11/stl.h>
#include <pybind11/cast.h>

namespace py = pybind11;

std::optional<std::pair<std::string, uint32_t>> get_fn_ln(uint32_t num_frame_back) {
    using namespace kratos;
    // get caller frame info
    PyFrameObject *frame = PyThreadState_Get()->frame;
    uint32_t i = 0;
    while (frame->f_back && (++i) < num_frame_back) {
        frame = frame->f_back;
    }
    if (frame) {
        uint32_t line_num = PyFrame_GetLineNumber(frame);
        struct py::detail::string_caster<std::string> repr;
        py::handle handle(frame->f_code->co_filename);
        repr.load(handle, true);
        if (repr) {
            // resolve full path
            std::string filename = fs::abspath(repr);
            return std::make_pair(filename, line_num);
        }
    }
    return std::nullopt;
}

void init_python_util(py::module &m) {
    m.def("get_fn_ln", []() {
       return get_fn_ln(1);
    })
    .def("get_fn_ln", [](uint32_t num_frame) {
        return get_fn_ln((num_frame));
    });
}