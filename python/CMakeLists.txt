set(PYBIND11_CPP_STANDARD -std=c++1z)

set(CMAKE_EXE_LINKER_FLAGS " -static")

pybind11_add_module(_kratos kratos.cc)
target_link_libraries(_kratos PRIVATE kratos)
target_link_libraries(_kratos PUBLIC -static-libgcc -static-libstdc++)

set_target_properties(_kratos PROPERTIES PREFIX "${PYTHON_MODULE_PREFIX}"
        SUFFIX "${PYTHON_MODULE_EXTENSION}" COMPILE_FLAGS "-Wno-register")