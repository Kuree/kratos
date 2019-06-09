cmake_minimum_required(VERSION 3.10)
project(dusk)

set(CMAKE_CXX_STANDARD 17)

# extern
add_subdirectory(extern/abseil-cpp)
add_subdirectory(extern/googletest/)

include(GoogleTest)

add_subdirectory(src)


enable_testing()
add_subdirectory(tests)

