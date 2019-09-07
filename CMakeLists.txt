cmake_minimum_required(VERSION 3.10)
project(kratos)

set(CMAKE_CXX_STANDARD 17)

# turn every warnings on
set(CMAKE_CXX_FLAGS "-Wall -g -Wextra -Werror -fPIC")

include(CheckCXXCompilerFlag)
CHECK_CXX_COMPILER_FLAG(-funroll-all-loops UNROLL)
if (${UNROLL})
    # osx's clang doesn't support it (travis)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -funroll-all-loops")
endif()

CHECK_CXX_COMPILER_FLAG(-static-libgcc COMPILER_STATIC)
if (${COMPILER_STATIC})
    set(STATIC_FLAG "-static-libgcc -static-libstdc++")
else()
    set(STATIC_FLAG "")
endif()

# extern
add_subdirectory(extern/googletest/)
add_subdirectory(extern/fmt)
add_subdirectory(extern/pybind11)
add_subdirectory(extern/sqlite)

include(GoogleTest)

add_subdirectory(src)
add_subdirectory(python)

enable_testing()
add_subdirectory(tests)
