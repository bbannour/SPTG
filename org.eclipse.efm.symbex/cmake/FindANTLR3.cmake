# =============================================================================
#           CMake package looking for ANTLR3 C runtime librairies 
# =============================================================================
#
# ANTLR3_FOUND        : System has ANTLR3 C Runtime lib and associated headers
# ANTLR3_LIBRARIES    : ANTLR3 library location 
# ANTLR3_INCLUDE_DIR  : ANTLR3 include directory
#
# Note : this package is not designed to be general nor comprehensive : 
#        it only fits the Symbex project needs
#
# =============================================================================

if (ANTLR3_INCLUDE_DIR AND ANTLR3_LIBRARIES) # Already in cache, be silent
	set (ANTLR3_FIND_QUIETLY TRUE)
endif ()

find_path (ANTLR3_INCLUDE_DIR NAMES antlr3.h HINTS ${ANTLR3_INSTALL_INCLUDE_DIR})
find_library (ANTLR3_LIBRARIES NAMES libantlr3c libantlr3c.a HINTS ${ANTLR3_INSTALL_LIB_DIR} ${CVC4_INSTALL_LIB_DIR})
message (STATUS "ANTLR3 : " ${ANTLR3_LIBRARIES} " " ${ANTLR3_INCLUDE_DIR})

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args (ANTLR3 DEFAULT_MSG ANTLR3_LIBRARIES ANTLR3_INCLUDE_DIR)

