cmake_minimum_required(VERSION 3.10)
project(kratos)

set(CMAKE_CXX_STANDARD 17)

# turn every warnings on
# set(CMAKE_CXX_FLAGS "-Wall -Wextra -Werror -fPIC")

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

# filesystem
include(CheckCXXSourceCompiles)
set(CMAKE_REQUIRED_LIBRARIES stdc++fs)
CHECK_CXX_SOURCE_COMPILES("
#include <filesystem>
int main() {
  std::filesystem::exists(\"\");
  std::filesystem::path p = \"\";
  std::string r = p / p;
}
" INCLUDE_FILESYSTEM)
# disable it on APPLE since it doesn't allow static linking
if (APPLE)
    SET(INCLUDE_FILESYSTEM 0)
endif()
if (${INCLUDE_FILESYSTEM})
    # This should be ideally add_compile_definitions() in the long term, but
    # that's not available until CMake 3.12 and we don't want to cut off people
    # on older versions.
    add_definitions(-DINCLUDE_FILESYSTEM)
else()
    MESSAGE(WARNING "<filesystem> not found. Fall back to C implementation")
    set(CMAKE_REQUIRED_LIBRARIES "")
    CHECK_CXX_SOURCE_COMPILES("
#include <cstdlib>
int main() {
    realpath(\"\", nullptr);
}

" NO_FS_HAS_REALPATH)
    if (${NO_FS_HAS_REALPATH})
        add_definitions(-DNO_FS_HAS_REALPATH)
    else()
        MESSAGE(WARNING "realpath not found. Trying to use windows API")
    endif()
endif()

# unset CMAKE_REQUIRED_LIBRARIES
set(CMAKE_REQUIRED_LIBRARIES "")

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
