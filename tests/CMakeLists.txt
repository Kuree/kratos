# test files
file(GLOB TEST_VECTORS ${CMAKE_CURRENT_SOURCE_DIR}/vectors/*.sv)
foreach (_test_file ${TEST_VECTORS})
    get_filename_component(_test_name ${_test_file} NAME)
    configure_file(${_test_file}
            ${CMAKE_CURRENT_BINARY_DIR}/${_test_name} COPYONLY)
endforeach ()

add_executable(test_generator test_generator.cc)
target_link_libraries(test_generator gtest kratos gtest_main)
gtest_discover_tests(test_generator
        WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/vectors)

add_executable(test_expr test_expr.cc)
target_link_libraries(test_expr gtest kratos gtest_main)
gtest_discover_tests(test_expr
        WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/vectors)

add_executable(test_stmt test_stmt.cc)
target_link_libraries(test_stmt gtest kratos gtest_main)
gtest_discover_tests(test_stmt
        WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/vectors)

add_executable(test_ir test_ir.cc)
target_link_libraries(test_ir gtest kratos gtest_main)
gtest_discover_tests(test_ir
        WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/vectors)

add_executable(test_tb test_tb.cc)
target_link_libraries(test_tb gtest kratos gtest_main)
gtest_discover_tests(test_tb
        WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/vectors)

add_executable(test_debug test_debug.cc)
target_link_libraries(test_debug gtest kratos gtest_main)
gtest_discover_tests(test_debug
        WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/vectors)

add_executable(test_sim test_sim.cc)
target_link_libraries(test_sim gtest kratos gtest_main)
gtest_discover_tests(test_sim
        WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/vectors)

add_executable(test_lib test_lib.cc)
target_link_libraries(test_lib gtest kratos gtest_main)
gtest_discover_tests(test_lib
        WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/vectors)

add_executable(test_fault test_fault.cc)
target_link_libraries(test_fault gtest kratos gtest_main)
gtest_discover_tests(test_fault
        WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/vectors)