# =============================================================================
#                    CMake Master File for Symbex Unit Tests
# =============================================================================
#

# Minimum required CMake version
cmake_minimum_required (VERSION 2.8 FATAL_ERROR)

# Tell cmake where to find its own modules
list (APPEND CMAKE_MODULE_PATH ${CMAKE_SOURCE_DIR}/utests/cmake)
list (APPEND CMAKE_MODULE_PATH ${CMAKE_SOURCE_DIR}/cmake)

# Print title banner
set (BANNER_MESSAGE "This is Symbex Unit Test")
include (PrintBanner)

# Searching for Symbex internal libraries
# Unit tests are built against Symbex internal libraries and look for them in SYMBEX_BINARY_DIR
# The following line suppose they have been built in builds/... (default location)
set (SYMBEX_BINARY_DIR ${CMAKE_BINARY_DIR}/..)
include (LookForSymbexLibs)

# Project definition (directories hierarchy, main target sources, link)
include (DefineSymbexUnitTestProject)
