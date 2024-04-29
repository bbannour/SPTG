# =============================================================================
#
#                 Master CMake File for Diversity / Symbex 
#
# =============================================================================
#   Author: CEA LIST 
# =============================================================================


# Minimum required CMake version
cmake_minimum_required (VERSION 3.6 FATAL_ERROR)

# Project definition
project (Symbex_all CXX C)
set (CMAKE_CXX_STANDARD 17)
set (CMAKE_CXX_STANDARD_REQUIRED ON)

# Tell cmake where to find its own modules
list (APPEND CMAKE_MODULE_PATH ${CMAKE_SOURCE_DIR}/cmake)

# Banner
include (PrintBanner)

# Get info from the environment
include (DetectSystem)
include (DetectToolChain)
include (DetectSourcesRevision)

#add_compile_options (-fmessage-length=0 -pipe -fPIC -fpermissive)

# Set the various build options
include (SelectOptions)

# Set the platform specific options
include (SelectPlatform)

# Define the target to build
include (DefineTarget)

# Load prerequisites if needed
# Deprecated --> remove support
#include (LoadANTLR2)

include (LoadANTLR3C)
include (LoadANTLR4)
include (LoadBoost)
include (LoadCVC4)
include (LoadGMP)
include (LoadOmega)
include (LoadPython3)
include (LoadYices2)
include (LoadZ3)
include (LoadProtobuf)
include (LoadGRPC)
include (FindProtobuf)


# Generate informative header files
include (GenerateInfoHeaders)

# Include header directories from all previous searchs
# and set general compilation options
include_directories (${INC_DIRECTORIES})

# Define project structure (internal libraries)
include (DefineProjectHierarchy)

message (STATUS "Current EXTERNAL_LIBRARIES: ${EXTERNAL_LIBRARIES}")


# Define link of the main target(s)
include (LinkTarget)

# Summary (Debug)
#formatprint (100 "=" "" "" " Summary ")
#listprint("${EXTERNAL_LIBRARIES}")
#listprint("${INC_DIRECTORIES}")




## ======== BUILD CONFIGURATION ============================================
#message("")
#message("")
#message("* * * * * * * * * * Build type configuration for Symbex all * * * * * * * * * *")

#if(DEFINED ENV{DIVERSITY_CMAKE_BUILD_TYPE})
	#if($ENV{DIVERSITY_CMAKE_BUILD_TYPE} STREQUAL "TEST_AND_COVERAGE_UTESTS")
		#message("                    Using unitary test build configuration : $ENV{DIVERSITY_CMAKE_BUILD_TYPE}")
	#elseif($ENV{DIVERSITY_CMAKE_BUILD_TYPE} STREQUAL "PRODUCTION")
		#message("                    Using production build configuration : $ENV{DIVERSITY_CMAKE_BUILD_TYPE}")
	#else()
		#message( WARNING "                    Not using the org.eclipse.efm.cdash.ctest build configuration framework : default symbex.exe configuration used")
		#message("                    placeholder : $ENV{DIVERSITY_CMAKE_BUILD_TYPE}")
	#endif()
#endif()

#message("")
#message("")


## for specific builds
#if(DEFINED ENV{DIVERSITY_CMAKE_BUILD_TYPE})
	#if($ENV{DIVERSITY_CMAKE_BUILD_TYPE} STREQUAL "TEST_AND_COVERAGE_UTESTS")
		## Load testing facilities
		## it must be done on the highest level cmakelists.txt otherwise ctest does not find the tests :
		## see http://stackoverflow.com/questions/13550153/no-tests-found-when-using-gtest-with-cmake-ctest
		#include (CTest)
		## coverage
		#include(InitCoverage)
		#add_subdirectory (utests)
	#endif()
#endif()
