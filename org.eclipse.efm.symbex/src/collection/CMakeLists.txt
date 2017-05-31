# =============================================================================
#                   CMake file for the COLLEC library
# =============================================================================

# C++ source files to take into account (all files matching patterns recursively)
file (GLOB_RECURSE COLLEC_CXX_SRC_FILES *.cpp *.h)

# Target to build
add_library (collection STATIC ${COLLEC_CXX_SRC_FILES})

# Include directories (internal)
target_include_directories (collection PUBLIC ..) # FIXME : explicit the dependencies lib by lib

