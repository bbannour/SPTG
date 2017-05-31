# =============================================================================
#                    CMake file for the UTIL library
# =============================================================================

# C++ source files to take into account (all files matching patterns)
file (GLOB UTIL_CXX_SRC_FILES *.cpp *.h)

# Target to build
add_library (util STATIC ${UTIL_CXX_SRC_FILES})

# Include directories (internal)
target_include_directories (util PUBLIC ..) # FIXME : explicit the dependencies lib by lib

# Target include directories (external)
target_include_directories (util PUBLIC ${GMP_INCLUDE_DIR} ${GMPXX_INCLUDE_DIR})
target_include_directories (util PUBLIC ${Boost_INCLUDE_DIRS})
