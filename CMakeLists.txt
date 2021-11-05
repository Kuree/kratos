cmake_minimum_required(VERSION 3.10)
project(kratos)

set(CMAKE_CXX_STANDARD 17)

# turn every warnings on
if (NOT WIN32)
    set(CMAKE_CXX_FLAGS "-Wall -Wextra -Werror -fPIC")
else()
    # windows has more strict checks on stuff that we have no control over
    # in this case it's sqlite.h header
    set(CMAKE_CXX_FLAGS "-Wno-language-extension-token")
endif()

############# coverage #############
if (DEFINED ENV{KRATOS_COVERAGE})
    SET(GCC_COVERAGE_COMPILE_FLAGS "-fprofile-arcs -ftest-coverage")
    SET(GCC_COVERAGE_LINK_FLAGS    "-lgcov")
    # use O0 without any optimization
    SET(CMAKE_CXX_FLAGS  "${CMAKE_CXX_FLAGS} ${GCC_COVERAGE_COMPILE_FLAGS} -O0")
    SET(CMAKE_EXE_LINKER_FLAGS  "${CMAKE_EXE_LINKER_FLAGS} ${GCC_COVERAGE_LINK_FLAGS}")
endif()

############# compiler optimization flags #############
include(CheckCXXCompilerFlag)
CHECK_CXX_COMPILER_FLAG(-funroll-all-loops UNROLL)
if (${UNROLL})
    # osx's clang doesn't support it (travis)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -funroll-all-loops")
endif()

CHECK_CXX_COMPILER_FLAG(-static-libgcc COMPILER_STATIC)
if (${COMPILER_STATIC})
    # we also need to hide all symbols, other we will run into cxx string ABI issue
    # https://stackoverflow.com/a/57077456
    set(STATIC_FLAG "-static-libgcc -static-libstdc++")
    if(UNIX AND NOT APPLE)
        # only for Linux
        set(STATIC_FLAG ${STATIC_FLAG} -Wl,--exclude-libs,ALL)
    endif()
else()
    set(STATIC_FLAG "")
endif()

############# filesystem #############
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


############# external libraries #############
add_subdirectory(extern/googletest/)
add_subdirectory(extern/fmt)
add_subdirectory(extern/pybind11)
add_subdirectory(extern/sqlite)


############# Tests #############
include(GoogleTest)
include (CTest)

add_subdirectory(src)
add_subdirectory(python)

enable_testing()
add_subdirectory(tests)
