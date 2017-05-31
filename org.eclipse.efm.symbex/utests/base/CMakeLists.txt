# =============================================================================
#                      CMake file for the Base library testing
# =============================================================================

message (STATUS "****** Defining unit tests ******")


# Define Test runner for the base library
file (GLOB_RECURSE T_BASE_CXX_SRC_FILES t_*.cpp t_*.h)

add_executable(t_base_runner ${T_BASE_CXX_SRC_FILES})


# Find header required to compile the test runner 
target_include_directories (t_base_runner PUBLIC ${Boost_INCLUDE_DIRS})
target_include_directories (t_base_runner PUBLIC ../../src)

# Link required librairies to the test runner
#target_link_libraries(t_base_runner base ${Boost_LIBRARY_DIRS}/libboost_unit_test_framework-mt.a)
target_link_libraries(t_base_runner base ${Boost_LIBRARY_DIRS}/libboost_unit_test_framework.a)

# Define tests
add_test (NAME t_InstanceCounter_all COMMAND t_base_runner --log_level=test_suite --run_test=Base/t_InstanceCounter_all)

