set(PYBIND11_CPP_STANDARD -std=c++1z)

set(CMAKE_EXE_LINKER_FLAGS " -static")

pybind11_add_module(_kratos kratos.cc kratos_expr.cc kratos_expr.hh kratos_pass.cc kratos_generator.cc
        kratos_debug.hh kratos_stmt.cc kratos_fsm.cc kratos_except.cc kratos_tb.cc kratos_debug.cc
        kratos_enum.cc kratos_python.cc)
target_link_libraries(_kratos PRIVATE kratos)
target_link_libraries(_kratos PUBLIC ${STATIC_FLAG})

set_target_properties(_kratos PROPERTIES PREFIX "${PYTHON_MODULE_PREFIX}"
        SUFFIX "${PYTHON_MODULE_EXTENSION}" COMPILE_FLAGS "-Wno-register")

if ("${CMAKE_CXX_COMPILER_ID}" STREQUAL "Clang")
    set_target_properties(_kratos PROPERTIES COMPILE_FLAGS -fsized-deallocation)
endif()