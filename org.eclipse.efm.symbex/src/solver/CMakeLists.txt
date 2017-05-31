# =============================================================================
#                  CMake file for the SOLVER library 
# =============================================================================

# C++ source files to take into account (all files matching patterns recursively)
file (GLOB_RECURSE SOLVER_CXX_SRC_FILES *.cpp *.h)

# Target to build
add_library (solver STATIC ${SOLVER_CXX_SRC_FILES})

# Include directories (internal)
target_include_directories (solver PUBLIC ..) # FIXME : explicit the dependencies lib by lib

# Target include directories (external)
target_include_directories (solver PUBLIC ${GMP_INCLUDE_DIR} ${GMPXX_INCLUDE_DIR})
target_include_directories (solver PUBLIC ${Boost_INCLUDE_DIRS})
target_include_directories (solver PUBLIC ${CVC4_INCLUDE_DIR} ${CVC4_INCLUDE_DIR}/cvc4) # FIXME (confusion between include/cvc4 or include/cvc4/cvc4)


add_dependencies(solver rescan_cvc4)
