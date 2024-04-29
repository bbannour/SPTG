# ==============================================================================
#            CMake module: Loading Omega libraries if needed 
# ==============================================================================

option (WITH_OMEGA "Use polyhedral computation" OFF) # Default: non

if (WITH_OMEGA)

	include(Utils)
	formatprint (100 "=" "" "" " Looking for: Omega ")

	find_package (Omega)
	
	if (Omega_FOUND)
	  message (STATUS "Includes : " ${Omega_INCLUDES})
	  message (STATUS "Libraries: " ${Omega_LIBRARIES})
	  add_definitions (-D_AVM_SOLVER_OMEGA_)
	  message (STATUS)
	else()
	  message (FATAL_ERROR "Omega not found")
	endif()


	
endif()
