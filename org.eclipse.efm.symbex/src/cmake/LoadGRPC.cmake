# ==============================================================================
#            CMake module: Loading GRPC libraries if needed 
# ==============================================================================


if (WITH_GRPC_SERVER)
  
  include(Utils)
  formatprint (100 "=" "" "" " Looking for: GRPC ")
  
  find_package (GRPC)

	if (GRPC_FOUND)
	  message (STATUS "Includes : " ${GRPC_INCLUDE_DIR})
	  message (STATUS "Libraries: " ${GRPC_LIBRARIES})	  
	  add_definitions(-D_EXPERIMENTAL_SERVER_GRPC_FEATURE_)	  
      set (INC_DIRECTORIES ${INC_DIRECTORIES} ${GRPC_INCLUDE_DIR})
      set (EXTERNAL_LIBRARIES ${EXTERNAL_LIBRARIES} ${GRPC_LIBRARIES})
	  set (EXTERNAL_LIBRARIES ${EXTERNAL_LIBRARIES} ${GRPC_REFLECTION_LIBRARIES})
	  
	  message (STATUS)
	   
	else()
	  message (FATAL_ERROR "GRPC not found")
	endif()
	
endif()

