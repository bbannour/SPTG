# =============================================================================
#     CMake Module: looking for Software Configuration Management tools
# =============================================================================


formatprint (100 "=" "" "" " Looking for: Git ")

# Looking for Git
find_package(Git)

if (GIT_FOUND)
    message (STATUS "Git ${GIT_VERSION_STRING} found : ${GIT_EXECUTABLE}")
	execute_process (COMMAND                          ${GIT_EXECUTABLE} describe --long --tags --dirty --always
					 WORKING_DIRECTORY                ${CMAKE_SOURCE_DIR}
					 OUTPUT_VARIABLE                  GIT_COMMIT_ID
					 OUTPUT_STRIP_TRAILING_WHITESPACE
					)      
	message (STATUS "Commit id : ${GIT_COMMIT_ID}")   
else ()
    message (FATAL_ERROR "Git: not found")
endif()
