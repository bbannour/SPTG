# =============================================================================
#                    CMake file for the BUILDER library 
# =============================================================================

# C++ source files to take into account (all files matching patterns, recursively)
file (GLOB_RECURSE BUILDER_CXX_SRC_FILES *.cpp *.h)

# Target to build
add_library (builder STATIC ${BUILDER_CXX_SRC_FILES})

# Include directories (internal)
target_include_directories (builder PUBLIC ..) # FIXME : explicit the dependencies lib by lib

# Target include directories (external)
target_include_directories (builder PUBLIC ${GMP_INCLUDE_DIR} ${GMPXX_INCLUDE_DIR})
target_include_directories (builder PUBLIC ${Boost_INCLUDE_DIRS})
target_include_directories (builder PUBLIC ${CVC4_INCLUDE_DIR})

