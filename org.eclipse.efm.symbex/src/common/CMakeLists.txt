# =============================================================================
#                    CMake file for the COMMON library
# =============================================================================

# C++ source files to take into account (all files matching patterns recursively)
file (GLOB_RECURSE COMMON_CXX_SRC_FILES *.cpp *.h)

# Target to build
add_library (common STATIC ${COMMON_CXX_SRC_FILES})

# Include directories (internal)
target_include_directories (common PUBLIC ..)

# Target include directories (external)
target_include_directories (common PUBLIC ${GMP_INCLUDE_DIR} ${GMPXX_INCLUDE_DIR})
target_include_directories (common PUBLIC ${Boost_INCLUDE_DIRS})


