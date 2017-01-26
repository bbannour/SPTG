# =============================================================================
#       CMake module generating source files with useful information 
# =============================================================================


message (STATUS "****** Generating informative headers ******")


configure_file (${PROJECT_SOURCE_DIR}/src/main/version.h.in ${PROJECT_BINARY_DIR}/main/version.h)
configure_file (${PROJECT_SOURCE_DIR}/src/util/confs.h.in   ${PROJECT_BINARY_DIR}/util/confs.h)

include_directories(${PROJECT_BINARY_DIR}/main)
include_directories(${PROJECT_BINARY_DIR}/util)