# =============================================================================
#                      CMake file for the FML library testing
# =============================================================================


# Define Test runner for the FML library
file (GLOB_RECURSE T_FML_CXX_SRC_FILES t_*.cpp t_*.h)
add_executable(t_fml_runner ${T_FML_CXX_SRC_FILES})

# Find header required to compile the test runner 
target_include_directories (t_fml_runner PUBLIC ${Boost_INCLUDE_DIRS}) 
target_include_directories (t_fml_runner PUBLIC ../../src)

# Link required librairies to the test runner # FIXME : too much libraries and duplicates here
target_link_libraries(t_fml_runner base fam fml sew parser fam fml fam builder sew solver computer fml common collection printer util common ${ANTLR2_LIBRARIES} ${ANTLR3_LIBRARIES} ${Boost_LIBRARIES} ${CVC4_LIBRARIES} ${lib_gmp_c} ${lib_gmp_cxx})

# Define tests
list (APPEND TEST_NAMES t_integer_ctor  t_integer_big  t_integer_maxuint  t_integer_maxlong  t_integer_10pow123)
list (APPEND TEST_NAMES t_rational_ctor t_rational_big t_rational_maxuint t_rational_maxlong t_rational_decimal_big)
list (APPEND TEST_NAMES t_float_ctor    t_float_big    t_float_maxuint    t_float_maxlong) 
list (APPEND TEST_NAMES t_numeric_ctor  t_numeric_ctor_decimal_excp t_numeric_ctor_decimal t_numeric_ctor_frac t_numeric_frac_simplif)

# tests on optional libraries that are not yet integrated into diversity install process
#list (APPEND TEST NAMES t_ginac_expression_printing t_ginac_expression_not_or_substitution t_ginac_expression_not_and_substitution t_ginac_expression_and_or_composition_equivalence)
#list (APPEND TEST NAMES t_yices_expression_printing)

foreach (TEST_NAME ${TEST_NAMES})
    add_test (NAME ${TEST_NAME} COMMAND t_fml_runner --log_level=test_suite --run_test=FML/${TEST_NAME} )
endforeach()

