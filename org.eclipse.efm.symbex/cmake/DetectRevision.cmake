# =============================================================================
#       CMake module getting the git description of the current commit  
# =============================================================================


message (STATUS "****** Looking for git commit id ******")


execute_process (COMMAND                         ${GIT_EXECUTABLE} describe --long --tags --dirty --always
                WORKING_DIRECTORY                ${CMAKE_SOURCE_DIR}
                OUTPUT_VARIABLE                  GIT_COMMIT_ID
                OUTPUT_STRIP_TRAILING_WHITESPACE
                )
                
message (STATUS "Commit id : ${GIT_COMMIT_ID}")
