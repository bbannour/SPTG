# ==============================================================================
#                 CMake module: define optional build features
# ==============================================================================
#
#  Main target options (at least one must chosen): 
#    BUILD_EXECUTABLE  (default:ON)
#    BUILD_PYTHONMODULE (default:ON)
#	 BUILD_PYVERSITYDEBUG (default:OFF)
#  Solver options (at least one must chosen):
#    WITH_Z3 (default:ON)
#    WITH_CVC4 (default:OFF)
#    WITH_YICE_V2 (default:OFF)
# 
#  Omega options:  
#    WITH_OMEGA (default: OFF)
#
#  Version options
#    EXPERIMENTAL_FEATURES: (default:OFF)
#
#  Unit tests options:
#    WITH_UNIT_TESTS (default: OFF)
#
# ==============================================================================


include(Utils)


formatprint (100 "=" "" "" " Build options ")

set (EXTERNAL_LIBRARIES)


# ============================= Target type ====================================
option (BUILD_EXECUTABLE   "build executable" ON)
option (BUILD_PYTHONMODULE "build shared library python module" ON)
option (BUILD_PYVERSITYDEBUG   "build pyversity Debug" OFF)

if (NOT BUILD_EXECUTABLE AND NOT BUILD_PYTHONMODULE)
  message (FATAL_ERROR "No target selected")

else()
  message (STATUS "Targets:")
  message (STATUS "  executable   : ${BUILD_EXECUTABLE}")
  message (STATUS "  python module: ${BUILD_PYTHONMODULE})")
  message (STATUS "  python debug module: ${BUILD_PYVERSITYDEBUG})")
endif()

add_definitions (-D_AVM_BUILT_WITH_CMAKE_)


# ================================ Solvers =====================================
option (WITH_Z3    "build with Z3 solver"     ON)
option (WITH_CVC4  "build with CVC4 solver"   OFF)
option (WITH_YICE2 "build with YICES2 solver" OFF)

if ((NOT WITH_Z3) AND (NOT WITH_CVC4) AND (NOT WITH_YICE2))
  message (FATAL_ERROR "No solver selected")
  
else()
  message (STATUS "Solvers:")
  message (STATUS "  Z3    : ${WITH_Z3}")
  message (STATUS "  CVC4  : ${WITH_CVC4}")
  message (STATUS "  YICES2: ${WITH_YICE2}")  
endif()


# =================================  Omega =====================================
option (WITH_OMEGA "build with Omega polyhedral" OFF)
message (STATUS "Omega polyhedral: ${WITH_OMEGA}")

if (WITH_OMEGA)
  add_definitions (-D_AVM_SOLVER_OMEGA_)
  
else()
  add_definitions (-U_AVM_SOLVER_OMEGA_)
  
endif()


# ========================== Experimental features =============================
option (EXPERIMENTAL_FEATURES OFF)
message (STATUS "Experimental features: ${EXPERIMENTAL_FEATURES}")

if (EXPERIMENTAL_FEATURES)
  # Use Boost numerics
  add_definitions (-D_AVM_BUILTIN_NUMERIC_BOOST_) 

else()
  add_definitions (-U_AVM_BUILTIN_NUMERIC_BOOST_)
  
endif()


option (WITH_GRPC_SERVER "build with GRPC server" ON)
if ( SERVER_GRPC_FEATURE )
  add_definitions(-D_EXPERIMENTAL_SERVER_GRPC_FEATURE_)
endif()
message (STATUS "GRPC Server: ${WITH_GRPC_SERVER}")


# ===============================  Unit tests ==================================
option (WITH_UNIT_TESTS OFF)
message (STATUS "Unit tests: ${WITH_UNIT_TESTS}")

# TODO


message(STATUS)




