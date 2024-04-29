# ==============================================================================
#         CMake module: Associate libraries to the main(s) target(s)
# ==============================================================================
#
# Note : To add a new libraries don't modify this file. Instead update the 
#        INTERNAL_LIBRARIES or EXTERNAL_LIBRARIES variable in the relevant
#        cmake files
#
# ==============================================================================


if (BUILD_EXECUTABLE)
	
	target_link_libraries (${EXECUTABLE_NAME} ${INTERNAL_LIBRARIES} ${EXTERNAL_LIBRARIES})
	
 endif()


if (BUILD_PYTHONMODULE)
	
	target_link_libraries (${PYTHONMODULE1_NAME} sew parser famcore fml builder solver computer fml common base collection printer util ${EXTERNAL_LIBRARIES})
	target_link_libraries (${PYTHONMODULE2_NAME} ${PYTHONMODULE1_NAME}  ${EXTERNAL_LIBRARIES})
	target_link_libraries (${PYTHONMODULE3_NAME} ${PYTHONMODULE1_NAME}  ${EXTERNAL_LIBRARIES})
#	target_link_libraries (${PYTHONMODULE2_NAME} ${PYTHONMODULE1_NAME} ${EXTERNAL_LIBRARIES})
#	target_link_libraries (${PYTHONMODULE3_NAME} ${PYTHONMODULE1_NAME}} ${EXTERNAL_LIBRARIES})

	
endif()

if (BUILD_PYVERSITYDEBUG)
	
	target_link_libraries (${PYVERSITYDEBUG_NAME} ${INTERNAL_LIBRARIES} ${EXTERNAL_LIBRARIES})
	
 endif()

