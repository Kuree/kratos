cmake_minimum_required(VERSION 3.0)
project(kratos-runtime)

set(CMAKE_CXX_STANDARD 11)

# turn every warnings on
set(CMAKE_CXX_FLAGS "-Wall -g -Wextra -Werror -fPIC")

add_library(kratos-runtime debug_runtime.cc)