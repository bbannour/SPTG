# ==============================================================================
#                 CMake module: define target to build
# ==============================================================================
#
#    Note : it is possible to build each target separately or simultaneously
#
# ==============================================================================




# ============================ Executable definition =========================== 

if (BUILD_EXECUTABLE)

  # Target name (must be unique)
  set (EXECUTABLE_NAME symbex)  

  # Target source files (all files matching patterns)
  file (GLOB_RECURSE EXECUTABLE_MAIN_CXX_SRC main/*.cpp main/*.h famdv/*.cpp famdv/*.h famsc/*.cpp famsc/*.h server/*.cpp server/*.cc server/*.h)
  list (FILTER EXECUTABLE_MAIN_CXX_SRC EXCLUDE REGEX .*/main/pyversity_main.cpp)

  if (NOT EXPERIMENTAL_FEATURES)

  endif()


  # Target definition as executable file and association to its source files
  add_executable (${EXECUTABLE_NAME} ${EXECUTABLE_MAIN_CXX_SRC})

endif()


# ========================== Python modules definition ========================= 

if (BUILD_PYTHONMODULE)
  
  # No "lib" prefix in the target library name
  set (CMAKE_SHARED_LIBRARY_PREFIX_CXX "")
  
  
  # ******** Python module 1 : Maat Core ********
  
  # Target name (must be unique)
  set (PYTHONMODULE1_NAME maatcore)

  # Target source files (all files matching patterns + filtering to exclude main)
  file (GLOB_RECURSE PYTHONMODULE1_SRC main/*.cpp main/*.h bindings/*.cpp bindings/*.h)
  list (FILTER PYTHONMODULE1_SRC EXCLUDE REGEX .*/main.cpp$)
  list (FILTER PYTHONMODULE1_SRC EXCLUDE REGEX .*/AvmMain.cpp$)
  list (FILTER PYTHONMODULE1_SRC EXCLUDE REGEX .*/AvmLauncher.cpp$)
  list (FILTER PYTHONMODULE1_SRC EXCLUDE REGEX .*/designvalidation_py.cpp$)
  list (FILTER PYTHONMODULE1_SRC EXCLUDE REGEX .*/systemcompliance_py.cpp$)
  list (FILTER PYTHONMODULE1_SRC EXCLUDE REGEX .*/pyversity_main.cpp$)
  list (FILTER PYTHONMODULE1_SRC EXCLUDE REGEX .*/FamExposer.cpp$)
     
  # Target definition as dynamic library and association to its source files
  add_library (${PYTHONMODULE1_NAME} SHARED ${PYTHONMODULE1_SRC})
  #add_library (${PYTHONMODULE1_NAME} ${PYTHONMODULE1_SRC})
  
  # Symbolic link of the python libraries to the notebook pyversity folder
  add_custom_target (pymod1_symlink ALL ${CMAKE_COMMAND} -E create_symlink ${CMAKE_BINARY_DIR}/${PYTHONMODULE1_NAME}.so ${CMAKE_SOURCE_DIR}/bindings/notebook/maat/${PYTHONMODULE1_NAME}.so)


  # ******** Python module 2 : Maat Design Validation ********
  
  # Target name (must be unique)
  set (PYTHONMODULE2_NAME maatdv)

  # Target source files (all files matching patterns + filtering to exclude main)
  file (GLOB_RECURSE PYTHONMODULE2_SRC bindings/designvalidation_py.cpp bindings/designvalidation_py.h famdv/*.cpp famdv/*.h)
  list (FILTER PYTHONMODULE2_SRC EXCLUDE REGEX .*/FamDesignValidationExposer.cpp$)
  
  # Target definition as dynamic library and association to its source files
  add_library (${PYTHONMODULE2_NAME} SHARED ${PYTHONMODULE2_SRC})
  
  # Symbolic link of the python libraries to the notebook pyversity folder
  add_custom_target (pymod2_symlink ALL ${CMAKE_COMMAND} -E create_symlink ${CMAKE_BINARY_DIR}/${PYTHONMODULE2_NAME}.so ${CMAKE_SOURCE_DIR}/bindings/notebook/maat/${PYTHONMODULE2_NAME}.so)


  # ******** Python module 3 : Maat System Compliance ********
  
  # Target name (must be unique)
  set (PYTHONMODULE3_NAME maatsc)

  # Target source files (all files matching patterns + filtering to exclude main)
  file (GLOB_RECURSE PYTHONMODULE3_SRC bindings/systemcompliance_py.cpp bindings/systemcompliance_py.h famsc/*.cpp famsc/*.h)


  # Target definition as dynamic library and association to its source files
  add_library (${PYTHONMODULE3_NAME} SHARED ${PYTHONMODULE3_SRC})
  
  # Symbolic link of the python libraries to the notebook pyversity folder
  add_custom_target (pymod3_symlink ALL ${CMAKE_COMMAND} -E create_symlink ${CMAKE_BINARY_DIR}/${PYTHONMODULE3_NAME}.so ${CMAKE_SOURCE_DIR}/bindings/notebook/maat/${PYTHONMODULE3_NAME}.so)


endif()

# ============================ pyversity debug =========================== 

if (BUILD_PYVERSITYDEBUG)

  # Target name (must be unique)
  set (PYVERSITYDEBUG_NAME pyversitydebug)
  
  # Target source files (all files matching patterns)
  file (GLOB_RECURSE BUILD_PYVERSITYDEBUG_CXX_SRC main/*.cpp main/*.h famdv/*.cpp famdv/*.h famsc/*.cpp famsc/*.h)
  list (FILTER BUILD_PYVERSITYDEBUG_CXX_SRC EXCLUDE REGEX .*/main/main.cpp)
  # Target definition as executable file and association to its source files
  add_executable (${PYVERSITYDEBUG_NAME} ${BUILD_PYVERSITYDEBUG_CXX_SRC})

endif()
