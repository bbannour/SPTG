# ==============================================================================
#            CMake module: Loading Yices2 libraries if needed 
# ==============================================================================

if (WITH_YICES2)
  
  include(Utils)
  formatprint (100 "=" "" "" " Looking for: Yices2 ")
  
  find_package (Yices2)

	if (Yices2_FOUND)
	  message (STATUS "Includes : " ${Yices2_INCLUDE_DIR})
	  message (STATUS "Libraries: " ${Yices2_LIBRARIES})
	    
    set (INC_DIRECTORIES ${INC_DIRECTORIES} ${Yices2_INCLUDE_DIR})
	  set (EXTERNAL_LIBRARIES ${EXTERNAL_LIBRARIES} ${Yices2_LIBRARIES})
	message (STATUS)
	   
	else()
	  message (FATAL_ERROR "Yices2 not found")
	endif()
	
endif()
