# =============================================================================
#                 CMake module defining the Symbex project
# =============================================================================


message (STATUS "****** Defining project******")

# Definition of project name and supported languages
project (Symbex CXX C)

# Project structure : only add directories associated with the build of an
# internal library (i.e. containing a CMakeLists.txt defining a target)
# Sources within subdirectories are taken into account by the recursive
# look-up (see the specific CMakeLists.txt)


# Main target C++ source files  (all files matching patterns)
file (GLOB_RECURSE MAIN_CXX_SRC_FILES main/*.cpp main/*.h)

# Main target definition (association to its sources)
add_executable (HippTest ${MAIN_CXX_SRC_FILES})

# Adhoc dependencies to force builds from sources (if a prerequisite is not found)
add_dependencies(HippTest rescan_cvc4)
add_dependencies(HippTest rescan_antlr2)

# Main target link - FIXME : duplicate fml and fam needed to link sucessfully
#target_link_libraries (HippTest)
target_link_libraries (HippTest  ${ANTLR2_LIBRARIES} ${ANTLR3_LIBRARIES} ${Boost_LIBRARIES} ${CVC4_LIBRARIES} ${lib_gmp_c} ${lib_gmp_cxx})

