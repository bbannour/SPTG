# =============================================================================
#           CMake package: Looking for ANTLR4 CPP runtime librairies 
# =============================================================================
#
# Optional input variable: 
#   ANTLR4_INSTALL_INCLUDE_DIR: Used as a hint to look for header files
#   ANTLR4_INSTALL_LIB_DIR    : Used as a hint to look for libraries
#
# Returned variables: 
#   ANTLR4_FOUND      : System has ANTLR4 CPP Runtime lib and associated headers
#   ANTLR4_LIBRARIES  : librarie(s) full path 
#   ANTLR4_INCLUDE_DIR: include directory full path
#
# =============================================================================


include (FindPackageHandleStandardArgs)


# If already in cache, be silent
if (ANTLR4_INCLUDE_DIR AND ANTLR4_LIBRARIES)
	set (ANTLR4_FIND_QUIETLY TRUE)
endif ()

# Looking for headers
find_path (ANTLR4_INCLUDE_DIR NAMES antlr4-runtime.h HINTS ${ANTLR4_INSTALL_INCLUDE_DIR})
                                              
# Looking for libraries
find_library (ANTLR4_LIBRARIES NAMES antlr4-runtime libantlr4 HINTS ${ANTLR4_INSTALL_LIB_DIR})

# Standard package definition
find_package_handle_standard_args (ANTLR4 REQUIRED_VARS ANTLR4_LIBRARIES ANTLR4_INCLUDE_DIR)

# Do not show these variables in configuration user tool
mark_as_advanced (ANTLR4_LIBRARIES ANTLR4_INCLUDE_DIR)
