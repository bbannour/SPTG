# =============================================================================
#                CMake module: displaying current toolchain 
# =============================================================================


include (Utils)


formatprint (100 "=" "" "" " Looking for: toolchain info ")


# No real detection here, only printing what CMake already knows 
message (STATUS "C++ compiler: " ${CMAKE_CXX_COMPILER} ", version " ${CMAKE_CXX_COMPILER_VERSION})
message (STATUS "C compiler  : " ${CMAKE_C_COMPILER} ", version " ${CMAKE_C_COMPILER_VERSION})
message (STATUS "Linker      : " ${CMAKE_LINKER})
message (STATUS)
