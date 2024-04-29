# ===============================================================================
#             CMake module : Loading the needed Boost Components 
# ===============================================================================


include(Utils)
formatprint (100 "=" "" "" " Looking for: Boost ")

# ====================== Define which components to load ========================

# Mandatory boost components 
#set (BOOST_COMPONENTS chrono filesystem regex system)

# Boost Unit tests
if (WITH_UNIT_TESTS)
  set (BOOST_COMPONENTS ${BOOST_COMPONENTS} unit_test_framework)
endif()

# Boost Python bindings
if (BUILD_PYTHONMODULE)
  if (NOT (Boost_LIB_PYTHON3))
     set (Boost_LIB_PYTHON3 python3)
  endif()

  set (BOOST_COMPONENTS ${BOOST_COMPONENTS} ${Boost_LIB_PYTHON3})
endif()


find_package (Boost 1.58 REQUIRED COMPONENTS ${BOOST_COMPONENTS}) 
# Note: BOOST_ROOT variable is used as a search hint by find_package

if (NOT (Boost_FOUND)) 
  message (FATAL_ERROR "Boost not found :")
else ()
  listprint ("${Boost_LIBRARIES}")
  message (STATUS "Includes : " ${Boost_INCLUDE_DIRS})
  message (STATUS "Libraries: " ${Boost_LIBRARY_DIRS})
    
  # Look only for shared libraries
	set(Boost_USE_STATIC_LIBS OFF)

	# Shut multithreading off
	set(Boost_USE_MULTITHREADED OFF)
	#
	set (INC_DIRECTORIES ${INC_DIRECTORIES} ${Boost_INCLUDE_DIRS})
	set (EXTERNAL_LIBRARIES ${EXTERNAL_LIBRARIES} ${Boost_LIBRARIES})
    message (STATUS)
endif()
