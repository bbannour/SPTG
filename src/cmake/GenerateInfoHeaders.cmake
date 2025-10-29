# =============================================================================
#       CMake module: generating source files with useful information 
# =============================================================================


include (Utils)
formatprint (100 "=" "" "" " Source generation ")

# Generate headers the binary folder
configure_file (${PROJECT_SOURCE_DIR}/main/version.h.in ${PROJECT_BINARY_DIR}/main/version.h)
configure_file (${PROJECT_SOURCE_DIR}/util/confs.h.in   ${PROJECT_BINARY_DIR}/util/confs.h)

# Tell cmake to search the binary folder for these generated headers
include_directories (${PROJECT_BINARY_DIR}/main)
include_directories (${PROJECT_BINARY_DIR}/util)

message (STATUS "Generated: ${PROJECT_BINARY_DIR}/main/version.h") 
message (STATUS "Generated: ${PROJECT_BINARY_DIR}/util/confs.h") 
message (STATUS)
