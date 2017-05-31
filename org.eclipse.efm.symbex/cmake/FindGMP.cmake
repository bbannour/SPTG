# =============================================================================
#               CMake package looking for GMP libraries
# =============================================================================
#
# GMP_FOUND        : System has both GMP lib and associated headers
#
# Note : this package is not designed to be general nor comprehensive : 
#        it only fits the Symbex project needs
#
# =============================================================================

# If already in cache, be silent
if (gmp_includedir AND gmpxx_includedir AND lib_gmp_c AND lib_gmp_cxx)
		set (GMP_FIND_QUIETLY TRUE)
endif ()



find_path (gmp_includedir NAMES gmp.h PATHS ${GMP_INCLUDEDIR})
find_path (gmpxx_includedir NAMES gmpxx.h PATHS ${GMP_INCLUDEDIR})

find_library(lib_gmp_c NAMES gmp libgmp.a PATHS ${GMP_LIBRARYDIR})
find_library(lib_gmp_cxx NAMES gmpxx libgmpxx.a PATHS ${GMP_LIBRARYDIR})



include(FindPackageHandleStandardArgs)
find_package_handle_standard_args (GMP DEFAULT_MSG lib_gmp_c lib_gmp_cxx gmp_includedir gmpxx_includedir)
















