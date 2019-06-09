cmake_minimum_required(VERSION 3.10)
project(dusk)

set(CMAKE_CXX_STANDARD 17)

add_subdirectory(src)

# extern
add_subdirectory(extern/abseil-cpp)