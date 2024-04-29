# =============================================================================
#                     CMake package: looking for Z3 libraries
# =============================================================================
#
# Optional input variable: 
#   Yices2_INSTALL_INCLUDE_DIR: Used as a hint to look for header files
#   Yices2_INSTALL_LIB_DIR    : Used as a hint to look for libraries
#
# Returned variables: 
#   Yices2_FOUND            : System has Yices2 lib and associated headers
#   Yices2_INCLUDE_DIR      : include directory full path
#   Yices2_LIBRARIES        : librarie(s) full path
#
# =============================================================================

include(FindPackageHandleStandardArgs)


# If already in cache, be silent
if (Yices2_INCLUDE_DIR AND Yices2_LIBRARIES)
	set (Yices2_FIND_QUIETLY TRUE)
endif()

# Looking for headers
find_path (Yices2_INCLUDE_DIR NAMES yices.h HINTS ${Yices2_INSTALL_INCLUDE_DIR})

# Looking for libraries
find_library (Yices2_LIBRARIES NAMES yices HINTS ${Yices2_INSTALL_LIB_DIR})

# Standard package definition
find_package_handle_standard_args (Yices2 DEFAULT_MSG Yices2_LIBRARIES Yices2_INCLUDE_DIR)

# Do not show these variables in configuration user tool
mark_as_advanced(Yices2_LIBRARIES Yices2_INCLUDE_DIR)



## Once done this will define
##  YICES2_FOUND - System has yices2
##  YICES2_INCLUDE_DIRS - The yices2 include directories
##  YICES2_LIBRARIES - The libraries needed to use yices2


#if (YICES2_HOME)
  #find_path(YICES2_INCLUDE_DIR yices.h PATHS "${YICES2_HOME}/include")
#else() 
  #find_path(YICES2_INCLUDE_DIR yices.h)
#endif()

#if (SALLY_STATIC_BUILD)
  #if (YICES2_HOME)
    #find_library(YICES2_LIBRARY libyices.a yices PATHS "${YICES2_HOME}/lib")
  #else() 
    #find_library(YICES2_LIBRARY libyices.a yices)
  #endif()
#else()
  #if (YICES2_HOME)
    #find_library(YICES2_LIBRARY yices PATHS "${YICES2_HOME}/lib")
  #else() 
    #find_library(YICES2_LIBRARY yices)
  #endif()
#endif()

## If library found, check the version
#if (YICES2_INCLUDE_DIR AND Yices2_FIND_VERSION)

	## Check version. It is in yices.h of the form 
	## 
	## #define __YICES_VERSION            2
  ## #define __YICES_VERSION_MAJOR      3
  ## #define __YICES_VERSION_PATCHLEVEL 0

  ## Extract version lines from yices.h
  #file(STRINGS "${YICES2_INCLUDE_DIR}/yices.h" __YICES_H_VERSIONS REGEX "#define __YICES_VERSION")
  #foreach(v __YICES_VERSION __YICES_VERSION_MAJOR __YICES_VERSION_PATCHLEVEL)
    #if("${__YICES_H_VERSIONS}" MATCHES ".*#define ${v}[ ]+([0-9]+).*")
      #set(${v} "${CMAKE_MATCH_1}")
    #endif()
  #endforeach()

  #set(__YICES_H_VERSION "${__YICES_VERSION}.${__YICES_VERSION_MAJOR}.${__YICES_VERSION_PATCHLEVEL}")

  ## Compare the found version to asked for version
  #if ("${__YICES_H_VERSION}" VERSION_LESS "${Yices2_FIND_VERSION}")
     #unset(YICES2_INCLUDE_DIR CACHE)
     #unset(YICES2_LIBRARY CACHE)
  #elseif (Yices2_FIND_VERSION_EXACT AND NOT "${__YICES_H_VERSION}" VERSION_EQUAL "${Yices2_FIND_VERSION}")
     #unset(YICES2_INCLUDE_DIR CACHE)
     #unset(YICES2_LIBRARY CACHE) 
  #endif()
#endif()

#set(YICES2_LIBRARIES ${YICES2_LIBRARY})
#set(YICES2_INCLUDE_DIRS ${YICES2_INCLUDE_DIR})

#include(FindPackageHandleStandardArgs)
#find_package_handle_standard_args(Yices2 DEFAULT_MSG YICES2_LIBRARY YICES2_INCLUDE_DIR)

#mark_as_advanced(YICES2_INCLUDE_DIR YICES2_LIBRARY)
