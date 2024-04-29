# ==============================================================================
#            CMake module: Loading GMP/GMPXX libraries if needed 
# ==============================================================================


if (NOT EXPERIMENTAL_FEATURES)

	include (Utils)

	formatprint (100 "=" "" "" " Looking for: GMP/GMPXX ")

	find_package (GMP 6.0.0)
	
	if (GMP_FOUND)
	  message (STATUS "Includes : " ${GMP_INCLUDES})
	  message (STATUS "Libraries: " ${GMP_LIBRARIES})
	  
	else()
	  message (FATAL_ERROR "GMP not found")
	endif()

	find_package (GMPXX)
	if (GMPXX_FOUND)
	  message (STATUS "Includes: " ${GMPXX_INCLUDE_DIR})
	  message (STATUS "Libraries: " ${GMPXX_LIBRARIES})

	else()
	  message (FATAL_ERROR "GMPXX not found")
    endif()
    
    set (INC_DIRECTORIES ${INC_DIRECTORIES} ${GMP_INCLUDES} ${GMPXX_INCLUDE_DIR})
	  set (EXTERNAL_LIBRARIES ${EXTERNAL_LIBRARIES} ${GMP_LIBRARIES} ${GMPXX_LIBRARIES})

	add_definitions (-D_AVM_BUILTIN_NUMERIC_GMP_)
    
    message (STATUS)
	
endif()
