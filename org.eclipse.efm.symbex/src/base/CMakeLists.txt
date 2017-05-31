# =============================================================================
#                      CMake file for the BASE library 
# =============================================================================

# C++ source files to take into account (all files matching patterns recursively)
file (GLOB_RECURSE BASE_CXX_SRC_FILES *.cpp *.h)

# Target to build
add_library (base STATIC ${BASE_CXX_SRC_FILES})

# Include directories (internal)
target_include_directories (base PUBLIC ..) # FIXME : explicit the dependencies lib by lib


# Target include directories (external)
target_include_directories (base PUBLIC ${GMP_INCLUDE_DIR} ${GMPXX_INCLUDE_DIR})
target_include_directories (base PUBLIC ${Boost_INCLUDE_DIRS})
