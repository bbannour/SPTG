# =============================================================================
#                    CMake Master File for Symbex All
# =============================================================================
#
# Note : This file defines the whole process 
#
# =============================================================================

# Minimum required CMake version
cmake_minimum_required (VERSION 2.8 FATAL_ERROR)

project (Symbex_all CXX C)

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
#set (BOOST_COMPONENTS system filesystem regex unit_test_framework)
set (BOOST_COMPONENTS system filesystem regex)
include (LookForMandatoryPrereq) 





# ======== BUILD CONFIGURATION ============================================
message("")
message("")
message("* * * * * * * * * * Build type configuration for Symbex all * * * * * * * * * *")

if(DEFINED ENV{DIVERSITY_CMAKE_BUILD_TYPE})
	if($ENV{DIVERSITY_CMAKE_BUILD_TYPE} STREQUAL "TEST_AND_COVERAGE_UTESTS")
		message("                    Using unitary test build configuration : $ENV{DIVERSITY_CMAKE_BUILD_TYPE}")
	elseif($ENV{DIVERSITY_CMAKE_BUILD_TYPE} STREQUAL "PRODUCTION")
		message("                    Using production build configuration : $ENV{DIVERSITY_CMAKE_BUILD_TYPE}")
	else()
		message( WARNING "                    Not using the org.eclipse.efm.cdash.ctest build configuration framework : default symbex.exe configuration used")
		message("                    placeholder : $ENV{DIVERSITY_CMAKE_BUILD_TYPE}")
	endif()
endif()

message("")
message("")



# adding the main directory containing the code for the main executable (symbex.exe)
add_subdirectory (src)

# for specific builds
if(DEFINED ENV{DIVERSITY_CMAKE_BUILD_TYPE})
	if($ENV{DIVERSITY_CMAKE_BUILD_TYPE} STREQUAL "TEST_AND_COVERAGE_UTESTS")
		# Load testing facilities
		# it must be done on the highest level cmakelists.txt otherwise ctest does not find the tests :
		# see http://stackoverflow.com/questions/13550153/no-tests-found-when-using-gtest-with-cmake-ctest
		include (CTest)
		# coverage
		include(InitCoverage)
		add_subdirectory (utests)
	endif()
endif()



message("")
message("")
message("")
message("")

