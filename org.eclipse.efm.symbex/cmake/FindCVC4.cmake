# =============================================================================
#                     CMake package looking for CVC4
# =============================================================================
#
# CVC4_FOUND        : System has CVC4 lib and associated headers
# CVC4_INCLUDE_DIR  : CVC4 include directory
# CVC4_LIBRARIES      : CVC4 lib location
#
# Note : this package is not designed to be general nor comprehensive : 
#        it only fits the Symbex project needs
#
# =============================================================================

# If already in cache, be silent
if (CVC4_INCLUDE_DIR AND CVC4_LIBRARIES) # Already in cache, be silent
		set (CVC4_FIND_QUIETLY TRUE)
endif ()

#message ("CVC4_INSTALL_INCLUDE_DIR=${CVC4_INSTALL_INCLUDE_DIR}")
#message ("CVC4_INSTALL_LIB_DIR=${CVC4_INSTALL_LIB_DIR}")

find_path (CVC4_INCLUDE_DIR NAMES cvc4/cvc4.h  HINTS ${CVC4_INSTALL_INCLUDE_DIR})
find_library(CVC4_LIBRARIES NAMES libcvc4.a HINTS ${CVC4_INSTALL_LIB_DIR})
#find_library(CVC4_LIBRARIES NAMES cvc4 HINTS /c/msys64/mingw64/usr/lib)

message (STATUS "CVC4 : " ${CVC4_LIBRARIES} " " ${CVC4_INCLUDE_DIR})

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args (CVC4 DEFAULT_MSG CVC4_LIBRARIES CVC4_INCLUDE_DIR)

