# =============================================================================
#            CMake module : define project structure  
# =============================================================================
#
#   Note 1 : Only add here the directories associated with the build of an
#   internal library (i.e. containing a CMakeLists.txt defining a target)
#   Sources within subdirectories not built as libraries are taken into account
#   by a recursive look-up (see DefineTarget.cmake and the various 
#   CMakeLists.txt)
#
#   Note 2 : All add_definition, add_compile_option, etc. must be stated before 
#   the add_directory commands
#
# =============================================================================


# Hierarchy of internal libraries
add_subdirectory (base)
add_subdirectory (builder)
add_subdirectory (collection)
add_subdirectory (common)
add_subdirectory (computer)
add_subdirectory (famcore)
add_subdirectory (fml)
add_subdirectory (parser)
add_subdirectory (printer)
add_subdirectory (sew)
add_subdirectory (solver)
add_subdirectory (util)

set (INTERNAL_LIBRARIES sew parser famcore fml famcore builder solver computer fml common base collection printer util)
