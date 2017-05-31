# =============================================================================
#                    CMake file for the FML library 
# =============================================================================

# C++ source files to take into account (all files matching patterns, recursively)
file (GLOB_RECURSE FML_CXX_SRC_FILES *.cpp *.h)

# Target to build
add_library (fml STATIC ${FML_CXX_SRC_FILES})

# Include directories (internal)
target_include_directories (fml PUBLIC ..) # FIXME : explicit the dependencies lib by lib

# Target include directories (external)
target_include_directories (fml PUBLIC ${GMP_INCLUDE_DIR} ${GMPXX_INCLUDE_DIR})
target_include_directories (fml PUBLIC ${Boost_INCLUDE_DIRS})
target_include_directories (fml PUBLIC ${CVC4_INCLUDE_DIR})


add_dependencies(fml rescan_cvc4)

