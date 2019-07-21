add_library(kratos port.cc port.hh generator.cc generator.hh
        expr.hh context.hh expr.cc context.cc
        codegen.cc codegen.hh stmt.cc stmt.hh pass.cc pass.hh
        ir.cc ir.hh graph.cc graph.hh hash.cc hash.hh util.cc util.hh except.cc except.hh)

target_include_directories(kratos PUBLIC ../extern/fmt/include ../extern/cxxpool/src)
target_link_libraries(kratos fmt)