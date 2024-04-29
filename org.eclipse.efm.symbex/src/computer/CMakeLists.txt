# =============================================================================
#                      CMake file for the COMPUTER library 
# =============================================================================


# C++ source files to take into account (all files matching patterns, recursively)
file (GLOB_RECURSE COMPUTER_CXX_SRC_FILES *.cpp *.h)

# Target to build
add_library (computer STATIC ${COMPUTER_CXX_SRC_FILES})

# Include directories (internal)
target_include_directories (computer PUBLIC ..) # FIXME : explicit the dependencies lib by lib

 # Target include directories (external)
target_include_directories (computer PUBLIC ${GMP_INCLUDE_DIR} ${GMPXX_INCLUDE_DIR})
target_include_directories (computer PUBLIC ${Boost_INCLUDE_DIRS})
target_include_directories (computer PUBLIC ${CVC4_INCLUDE_DIR})
