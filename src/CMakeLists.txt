add_library(dusk port.cc port.hh module.cc module.hh io.cc io.hh wire.cc
        wire.hh expr.hh context.hh expr.cc context.cc)

target_link_libraries(dusk PUBLIC slang)
target_include_directories(dusk PUBLIC ../extern/abseil-cpp)
target_include_directories(dusk PUBLIC ../extern/slang/include)