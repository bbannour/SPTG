# =============================================================================
#                     CMake package: looking for Z3 libraries
# =============================================================================
#
# Optional input variable: 
#   Z3_INSTALL_INCLUDE_DIR: Used as a hint to look for header files
#   Z3_INSTALL_LIB_DIR    : Used as a hint to look for libraries
#
# Returned variables: 
#   Z3_FOUND            : System has Z3 lib and associated headers
#   Z3_INCLUDE_DIR      : include directory full path
#   Z3_LIBRARIES        : librarie(s) full path
#
# =============================================================================


include(FindPackageHandleStandardArgs)


# If already in cache, be silent
if (Z3_INCLUDE_DIR AND Z3_LIBRARIES)
	set (Z3_FIND_QUIETLY TRUE)
endif()

# Looking for headers
find_path (Z3_INCLUDE_DIR NAMES z3.h HINTS ${Z3_INSTALL_INCLUDE_DIR})

# Looking for libraries
find_library (Z3_LIBRARIES NAMES z3 HINTS ${Z3_INSTALL_LIB_DIR})

# Standard package definition
find_package_handle_standard_args (Z3 DEFAULT_MSG Z3_LIBRARIES Z3_INCLUDE_DIR)

# Do not show these variables in configuration user tool
mark_as_advanced(Z3_LIBRARIES Z3_INCLUDE_DIR)


