add_library(dusk port.cc port.hh module.cc module.hh io.cc io.hh)

target_link_libraries(dusk absl::base absl::str_format absl::strings)
target_include_directories(dusk PUBLIC ../extern/abseil-cpp)