# ==============================================================================
#            CMake module: Loading ANTLR3C libraries if needed 
# ==============================================================================


if (NOT EXPERIMENTAL_FEATURES)

  include (Utils)

  formatprint (100 "=" "" "" " Looking for: Antlr3 C ")

  find_package (ANTLR3C)

  message (STATUS "Includes : " ${ANTLR3C_INCLUDE_DIR})
  message (STATUS "Libraries: " ${ANTLR3C_LIBRARIES})

  set (INC_DIRECTORIES ${INC_DIRECTORIES} ${ANTLR3C_INCLUDE_DIR})
  set (EXTERNAL_LIBRARIES ${EXTERNAL_LIBRARIES} ${ANTLR3C_LIBRARIES})

  message (STATUS)
  
endif()
