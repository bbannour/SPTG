# =============================================================================
#       CMake module getting the git description of the current commit  
# =============================================================================


message (STATUS "****** Execute HiPP World ******")


execute_process (COMMAND                         ${MAIN_CXX_SRC_FILES}/HippTest
                WORKING_DIRECTORY                ${CMAKE_SOURCE_DIR}
                )
