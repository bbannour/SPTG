# =============================================================================
#                       CMake file for the FAM library
# =============================================================================

# C++ source files to take into account (all files matching patterns, recursively)
file (GLOB_RECURSE FAM_CXX_SRC_FILES *.cpp *.h)

# Target to build
add_library (fam STATIC ${FAM_CXX_SRC_FILES})

# Include directories (internal)
target_include_directories (fam PUBLIC ..)
# TODO : the previous form is an "all-catch" : every header of the project can be accessed
# It is required because sources use relative path to src in their #include
# This probably should be refactored to make build dependencies explicit in the CMakeLists

# Target include directories (external)
target_include_directories (fam PUBLIC ${GMP_INCLUDE_DIR} ${GMPXX_INCLUDE_DIR})
target_include_directories (fam PUBLIC ${Boost_INCLUDE_DIRS})
target_include_directories (fam PUBLIC ${CVC4_INCLUDE_DIR})


add_dependencies(fam rescan_cvc4)
