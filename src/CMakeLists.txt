add_library(dusk port.cc port.hh generator.cc generator.hh
        expr.hh context.hh expr.cc context.cc code_gen.cpp code_gen.h stmt.cc stmt.hh pass.cc pass.hh)

target_link_libraries(dusk PUBLIC slang)
target_include_directories(dusk PUBLIC ../extern/abseil-cpp)
target_include_directories(dusk PUBLIC ../extern/slang/include)