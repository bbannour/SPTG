# =============================================================================
#                    CMake Master File for Symbex Build
# =============================================================================
#
# Note : This file defines the whole process 
#
# =============================================================================

# Minimum required CMake version
cmake_minimum_required (VERSION 2.8 FATAL_ERROR)

# Tell cmake where to find its own modules
list (APPEND CMAKE_MODULE_PATH ${CMAKE_SOURCE_DIR}/cmake) # Common modules
list (APPEND CMAKE_MODULE_PATH ${CMAKE_SOURCE_DIR}/src/cmake)    # Specific modules

set (BANNER_MESSAGE "This is HiPP Test Build System")
include (PrintBanner)


# Project definition (directories hierarchy, main target sources, link)
include (DefineSymbexProject)

