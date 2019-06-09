add_library(dusk ir/port.cc ir/port.hh ir/module.cc ir/module.hh)

target_link_libraries(dusk asbl)
target_include_directories(dusk PUBLIC ../extern/abseil-cpp)