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

# Print title banner
set (BANNER_MESSAGE "This is Symbex Build System")
include (PrintBanner)

# Generating information headers
include (GenerateInfoHeaders)

# Project definition (directories hierarchy, main target sources, link)
include (DefineSymbexProject)
