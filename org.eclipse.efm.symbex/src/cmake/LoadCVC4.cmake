# ==============================================================================
#            CMake module: Loading CVC4 libraries if needed 
# ==============================================================================


if (WITH_CVC4)
  
  include(Utils)
  formatprint (100 "=" "" "" " Looking for: CVC4 ")
  
  find_package (CVC4)

	if (CVC4_FOUND)
	  message (STATUS "Includes : " ${CVC4_INCLUDE_DIR})
	  message (STATUS "Libraries: " ${CVC4_LIBRARIES})
	  
    set (INC_DIRECTORIES ${INC_DIRECTORIES} ${CVC4_INCLUDE_DIR})
	set (EXTERNAL_LIBRARIES ${EXTERNAL_LIBRARIES} ${CVC4_LIBRARIES})
	message (STATUS)
	   
	else()
	  message (FATAL_ERROR "CVC4 not found")
	endif()
	
endif()
