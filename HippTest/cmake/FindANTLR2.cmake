# =============================================================================
#                CMake package looking for ANTLR2 librairies 
# =============================================================================
#
# ANTLR2_FOUND         : System has ANTLR2 lib and associated headers
# ANTLR2_LIBRARIES     : libantlr.a location
# ANTLR2_INCLUDE_DIR   : include directory
#
# Note : this package is not designed to be general nor comprehensive : 
#        it only fits the Symbex project needs
#
# =============================================================================


if (ANTLR2_INCLUDE_DIR AND ANTLR2_LIBRARIES) # Already in cache, be silent
    set (ANTLR2_FIND_QUIETLY TRUE)
endif ()

#find_path (ANTLR2_INCLUDE_DIR NAMES ANTLRException.hpp PATH_SUFFIXES antlr HINTS ${ANTLR2_INSTALL_INCLUDE_DIR})
find_path (ANTLR2_INCLUDE_DIR NAMES antlr/ANTLRException.hpp HINTS ${ANTLR2_INSTALL_INCLUDE_DIR})
find_library (ANTLR2_LIBRARIES NAMES antlr libantlr.a HINTS ${ANTLR2_INSTALL_LIB_DIR})

message (STATUS "ANTLR2 : " ${ANTLR2_LIBRARIES} " " ${ANTLR2_INCLUDE_DIR})

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args (ANTLR2 DEFAULT_MSG ANTLR2_LIBRARIES ANTLR2_INCLUDE_DIR)


