# ==============================================================================
#            CMake module: Loading Z3 libraries if needed 
# ==============================================================================


if (WITH_Z3)
  
  include(Utils)
  formatprint (100 "=" "" "" " Looking for: Z3 ")
  
  find_package (Z3)

	if (Z3_FOUND)
	  message (STATUS "Includes : " ${Z3_INCLUDE_DIR})
	  message (STATUS "Libraries: " ${Z3_LIBRARIES})
	  
    if (EXPERIMENTAL_FEATURES)
	    add_definitions (-D_AVM_SOLVER_Z3_)
    else()
      add_definitions (-D_AVM_SOLVER_Z3_C_)
    endif()
	  
    set (INC_DIRECTORIES ${INC_DIRECTORIES} ${Z3_INCLUDE_DIR})
	set (EXTERNAL_LIBRARIES ${EXTERNAL_LIBRARIES} ${Z3_LIBRARIES})
	message (STATUS)
	   
	else()
	  message (FATAL_ERROR "Z3 not found")
	endif()
	
endif()

