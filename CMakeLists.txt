cmake_minimum_required(VERSION 3.10)
project(kratos)

set(CMAKE_CXX_STANDARD 17)

# turn every warnings on
set(CMAKE_CXX_FLAGS "-Wall -g -Wextra -Werror -fPIC")

# extern
add_subdirectory(extern/googletest/)
add_subdirectory(extern/slang EXCLUDE_FROM_ALL)
add_subdirectory(extern/pybind11)

include(GoogleTest)

add_subdirectory(src)
add_subdirectory(python)

enable_testing()
add_subdirectory(tests)
