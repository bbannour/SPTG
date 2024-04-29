# ===============================================================================
#           CMake module : Looking for ANTLR3 C Library 
# ===============================================================================
#
# Optional input variable: 
#   ANTLR3_INSTALL_INCLUDE_DIR: Used as a hint to look for header files
#   ANTLR3_INSTALL_LIB_DIR, CVC4_INSTALL_LIB_DIR
#                             : Used as a hint to look for libraries
#
# Returned variables: 
#   ANTLR3_FOUND       : System has ANTLR3C lib and associated headers
#   ANTLR3C_LIBRARIES  : librarie(s) full path
#   ANTLR3C_INCLUDE_DIR: include directory full path
#
# =============================================================================


include (FindPackageHandleStandardArgs)


# If already in cache, be silent
if (ANTLR3C_INCLUDE_DIR AND ANTLR3C_LIBRARIES)
	set (ANTLR3C_FIND_QUIETLY TRUE)
endif ()

# Looking for headers
find_path (ANTLR3C_INCLUDE_DIR NAMES antlr3.h HINTS ${ANTLR3C_INSTALL_INCLUDE_DIR})

# Looking for libraries
find_library (ANTLR3C_LIBRARIES NAMES antlr3c HINTS ${ANTLR3C_INSTALL_LIB_DIR} ${CVC4_INSTALL_LIB_DIR} /usr/lib)

# Standard package definition
find_package_handle_standard_args (ANTLR3C REQUIRED_VARS ANTLR3C_LIBRARIES ANTLR3C_INCLUDE_DIR)

# Do not show these variables in configuration user tool
mark_as_advanced(ANTLR3C_LIBRARIES ANTLR3C_INCLUDE_DIR)
