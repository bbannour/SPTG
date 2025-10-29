# =============================================================================
#                     CMake package: looking for GRPC libraries
# =============================================================================
#
# Optional input variable: 
#   GRPC_INSTALL_INCLUDE_DIR: Used as a hint to look for header files
#   GRPC_INSTALL_LIB_DIR    : Used as a hint to look for libraries
#
# Returned variables: 
#   GRPC_FOUND            : System has GRPC lib and associated headers
#   GRPC_INCLUDE_DIR      : include directory full path
#   GRPC_LIBRARIES        : librarie(s) full path
#
# =============================================================================


include(FindPackageHandleStandardArgs)


# If already in cache, be silent
if (GRPC_INCLUDE_DIR AND GRPC_LIBRARIES)
	set (GRPC_FIND_QUIETLY TRUE)
endif()

# Looking for headers
#find_path (GRPC_INCLUDE_DIR NAMES grpc++.h HINTS ${GRPC_INSTALL_INCLUDE_DIR})
find_path (GRPC_INCLUDE_DIR grpc++.h HINTS "/usr/include/grpc++" )

# Looking for libraries
find_library (GRPC_LIBRARIES grpc++ )
find_library (GRPC_REFLECTION_LIBRARIES libgrpc++_reflection.so)

message (STATUS "GRPC_INCLUDE_DIR : " ${GRPC_INCLUDE_DIR})
message (STATUS "GRPC_LIBRARIES : " ${GRPC_LIBRARIES})
message (STATUS "GRPC_REFLECTION_LIBRARIES : " ${GRPC_REFLECTION_LIBRARIES})

# Standard package definition
find_package_handle_standard_args (GRPC DEFAULT_MSG GRPC_LIBRARIES GRPC_REFLECTION_LIBRARIES GRPC_INCLUDE_DIR)

# Do not show these variables in configuration user tool
mark_as_advanced(GRPC_LIBRARIES GRPC_INCLUDE_DIR)


