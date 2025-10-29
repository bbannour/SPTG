# ==============================================================================
#            CMake module: Loading Protobuf libraries if needed 
# ==============================================================================


if (WITH_GRPC_SERVER)
  
  include(Utils)
  formatprint (100 "=" "" "" " Looking for: Protobuf ")
  
  find_package (Protobuf)

	if (Protobuf_FOUND)
	  message (STATUS "Includes : " ${Protobuf_INCLUDE_DIR})
	  message (STATUS "Libraries: " ${Protobuf_LIBRARIES})	  
      set (INC_DIRECTORIES ${INC_DIRECTORIES} ${Protobuf_INCLUDE_DIR})
      set (EXTERNAL_LIBRARIES ${EXTERNAL_LIBRARIES} ${Protobuf_LIBRARIES})
	  message (STATUS)
	   
	else()
	  message (FATAL_ERROR "Protobuf not found")
	endif()
	
endif()

