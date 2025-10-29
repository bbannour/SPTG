# =============================================================================
#                  CMake package: Looking for CVC4 libraries
# =============================================================================
#
# Optional input variable: 
#   ANTLR4_INSTALL_INCLUDE_DIR: Used as a hint to look for header files
#   ANTLR4_INSTALL_LIB_DIR    : Used as a hint to look for libraries
#
# Returned variables: 
#   CVC4_FOUND        : System has CVC4 lib and associated headers
#   CVC4_LIBRARIES    : librarie(s) full path
#   CVC4_INCLUDE_DIR  : include directory full path
#
# =============================================================================


include(FindPackageHandleStandardArgs)


# If already in cache, be silent
if (CVC4_INCLUDE_DIR AND CVC4_LIBRARIES)
		set (CVC4_FIND_QUIETLY TRUE)
endif ()

# Looking for headers
find_path (CVC4_INCLUDE_DIR NAMES cvc4/cvc4.h HINTS ${CVC4_INSTALL_INCLUDE_DIR})

# Looking for libraries
find_library(CVC4_LIBRARIES NAMES cvc4 HINTS ${CVC4_INSTALL_LIB_DIR})

# Standard package definition
find_package_handle_standard_args (CVC4 REQUIRED_VARS CVC4_LIBRARIES CVC4_INCLUDE_DIR)

# Do not show these variables in configuration user tool
mark_as_advanced(CVC4_LIBRARIES CVC4_INCLUDE_DIR)
