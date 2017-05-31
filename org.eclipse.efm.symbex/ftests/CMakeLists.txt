# =============================================================================
#                      CMake file for functional testing 
# =============================================================================


# Minimum required CMake version
cmake_minimum_required (VERSION 2.8 FATAL_ERROR)


# Tell cmake where to find its own modules
list (APPEND CMAKE_MODULE_PATH ${CMAKE_SOURCE_DIR}/../cmake)
list (APPEND CMAKE_MODULE_PATH ${CMAKE_SOURCE_DIR}/cmake)

# Print title banner
set (BANNER_MESSAGE "This is Symbex Functional Test")
include (PrintBanner)


# UNDER PROGRESS

add_executable(ls IMPORTED)
set_property (TARGET ls     PROPERTY IMPORTED_LOCATION /usr/bin/ls)



# Define tests
add_test (NAME ls COMMAND c:/msys64/usr/bin/ls) # Dummy test