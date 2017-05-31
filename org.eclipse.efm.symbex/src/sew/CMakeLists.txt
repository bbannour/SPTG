# =============================================================================
#                       CMake file for the SEW library
# =============================================================================

# C++ source files to take into account (all files matching patterns)
file (GLOB_RECURSE SEW_CXX_SRC_FILES *.cpp *.h)

# Target to build
add_library (sew STATIC ${SEW_CXX_SRC_FILES})

# Include directories (internal)
target_include_directories (sew PUBLIC ..) # FIXME : explicit the dependencies lib by lib

# Target include directories (external)
target_include_directories (sew PUBLIC ${GMP_INCLUDE_DIR} ${GMPXX_INCLUDE_DIR})
target_include_directories (sew PUBLIC ${BOOST_ROOT})


