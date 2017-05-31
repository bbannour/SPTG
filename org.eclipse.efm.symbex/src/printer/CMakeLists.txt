# =============================================================================
#                    CMake file for the PRINTER library
# =============================================================================

# C++ source files to take into account (all files matching patterns)
file (GLOB PRINTER_CXX_SRC_FILES *.cpp *.h)

# Target to build
add_library (printer STATIC ${PRINTER_CXX_SRC_FILES})

# Include directories (internal)
target_include_directories (printer PUBLIC ..) # FIXME : explicit the dependencies lib by lib

# Target include directories (external)
target_include_directories (printer PUBLIC ${Boost_INCLUDE_DIRS})
