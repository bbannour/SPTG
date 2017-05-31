# =============================================================================
#                CMake module displaying current toolchain 
# =============================================================================

message (STATUS "****** Looking for toolchain information ******")

# No real detection here, only printing what CMake knows already
message (STATUS "C++ compiler: " ${CMAKE_CXX_COMPILER} ", version " ${CMAKE_CXX_COMPILER_VERSION})
message (STATUS "C compiler: " ${CMAKE_C_COMPILER} ", version " ${CMAKE_C_COMPILER_VERSION})
message (STATUS "Linker: " ${CMAKE_LINKER})
