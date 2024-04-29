# ==============================================================================
#            CMake module: Loading ANTLR4 libraries if needed 
# ==============================================================================


if (NOT EXPERIMENTAL_FEATURES)

	include(Utils)

	formatprint (100 "=" "" "" " Looking for: ANTLR4 ")

	find_package (ANTLR4)
	
	if (ANTLR4_FOUND)
	  message (STATUS "Includes : " ${ANTLR4_INCLUDE_DIR})
	  message (STATUS "Libraries: " ${ANTLR4_LIBRARIES})
	  
	else()
    message (FATAL_ERROR "ANTLR4 not found")
    
	endif()

   
  set (INC_DIRECTORIES ${INC_DIRECTORIES} ${ANTLR4_INCLUDE_DIR})
	set (EXTERNAL_LIBRARIES ${EXTERNAL_LIBRARIES} ${ANTLR4_LIBRARIES})
   
  message (STATUS)
	
endif()
