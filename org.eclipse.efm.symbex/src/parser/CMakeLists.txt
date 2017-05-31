# =============================================================================
#                CMake file for the Parser library 
# =============================================================================


# Source files to take into account (all files matching patterns, recursively)
file (GLOB_RECURSE PARSER_CXX_SRC_FILES *.cpp *.h *.c)
file (GLOB_RECURSE PARSER_C_SRC_FILES *.c)

# Awfull hack to force C++ compilation (this C file actually includes a <algorithm> TL header...)
# TODO : Fix this in sources
set_source_files_properties (${PARSER_C_SRC_FILES} PROPERTIES LANGUAGE CXX )

# Target to build
add_library (parser STATIC ${PARSER_CXX_SRC_FILES})

# Include directories (internal)
target_include_directories (parser PUBLIC ..) # FIXME : explicit the dependencies lib by lib

# Target include directories (external)
target_include_directories (parser PUBLIC ${ANTLR_INCLUDE_DIR} ${ANTLR3C_INCLUDE_DIR})


add_dependencies(parser rescan_cvc4)
add_dependencies(parser rescan_antlr2)
