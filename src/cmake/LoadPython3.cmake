# ==============================================================================
#            CMake module: Loading Python3 libraries if needed 
# ==============================================================================


if (BUILD_PYTHONMODULE)
	include(Utils)

	formatprint (100 "=" "" "" " Looking for: Python3 ")

	set (Python_ADDITIONAL_VERSIONS 3.5)
	find_package(PythonLibs 3 REQUIRED)

	if (NOT (PYTHONLIBS_FOUND))
	  message (FATAL_ERROR "Python3 not found")
	else ()
	  message (STATUS "Include: " ${PYTHON_INCLUDE_DIRS})
	  message (STATUS "Libraries: " ${PYTHON_LIBRARIES})
		
	  set (INC_DIRECTORIES ${INC_DIRECTORIES} ${PYTHON_INCLUDE_DIRS})
	  set (EXTERNAL_LIBRARIES ${EXTERNAL_LIBRARIES} ${PYTHON_LIBRARIES})
		
		message (STATUS)
	endif()
endif()
