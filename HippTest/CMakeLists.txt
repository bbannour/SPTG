# =============================================================================
#                    CMake Master File for Symbex All
# =============================================================================
#
# Note : This file defines the whole process 
#
# =============================================================================

# Minimum required CMake version
cmake_minimum_required (VERSION 2.8 FATAL_ERROR)

project (HippTest_all CXX C)

# Tell cmake where to find its own modules
list (APPEND CMAKE_MODULE_PATH ${CMAKE_SOURCE_DIR}/cmake) # Common modules

# System detection
include (DetectSystem)

# Toolchain detection
include (DetectToolChain)

# Searching for configuration management tools 
include (LookForSCM)

# Sources revision
include (DetectRevision)

# Generic options that should propagate to all subtargets
# (hence they must be loaded before the project structure is defined)
include (GenericOptions)

# OS-specific options that should propagate to all subtargets 
# (hence they must be loaded before the project structure is defined)
include (SelectSpecificOptions)

# Searching for mandatory prerequisites
include (LookForMandatoryPrereq) 





# ======== BUILD CONFIGURATION ============================================
message("")
message("* * * * * * * * * * Build type configuration for HippTest all * * * * * * * * * *")

message("")



# adding the main directory containing the code for the main executable (hipp_test.exe)
add_subdirectory (src)
