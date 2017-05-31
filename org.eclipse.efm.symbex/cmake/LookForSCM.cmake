# =============================================================================
#     CMake Module looking for Software Configuration Management tools
# =============================================================================
#
# Note : Tools currently looked for are :  Git SVN
#
# =============================================================================



# Looking foir Git
find_package(Git)
if (GIT_FOUND)
    message (STATUS "Git ${GIT_VERSION_STRING} found : ${GIT_EXECUTABLE}" )
else ()
    message (FATAL_ERROR "Git not found")
endif()



# Looking for Mercurial
find_package(Hg)
if (HG_FOUND)
    message (STATUS "Mercurial ${HG_VERSION_STRING} found : ${HG_EXECUTABLE}" )
else ()
    message (STATUS "Mercurial not found")
endif()
