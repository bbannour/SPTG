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
add_subdirectory (base)
add_subdirectory (builder)
add_subdirectory (collection)
add_subdirectory (common)
add_subdirectory (computer)
add_subdirectory (compat)
add_subdirectory (fam)
add_subdirectory (fml)
add_subdirectory (parser)
add_subdirectory (printer)
add_subdirectory (sew)
add_subdirectory (solver)
add_subdirectory (util)



# Main target C++ source files  (all files matching patterns)
file (GLOB_RECURSE MAIN_CXX_SRC_FILES main/*.cpp main/*.h)

# Main target definition (association to its sources)
add_executable (symbex ${MAIN_CXX_SRC_FILES})

# Adhoc dependencies to force builds from sources (if a prerequisite is not found)
add_dependencies(symbex rescan_cvc4)
add_dependencies(symbex rescan_antlr2)

# Main target link - FIXME : duplicate fml and fam needed to link sucessfully
target_link_libraries (symbex sew parser fam fml fam builder solver computer fml common base collec compat printer util ${ANTLR2_LIBRARIES} ${ANTLR3_LIBRARIES} ${Boost_LIBRARIES} ${CVC4_LIBRARIES} ${lib_gmp_c} ${lib_gmp_cxx})

