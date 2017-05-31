# =============================================================================
#                 Setup of Native Linux specific options
# =============================================================================
#
#
# =============================================================================


message (STATUS "****** Setting options for Linux/GCC ******")

# Compilation directives
add_definitions     (-D__AVM_UNIX__ -D__AVM_LINUX__)
add_compile_options (-fmessage-length=0 -pipe)


SET( CMAKE_EXE_LINKER_FLAGS  "${CMAKE_EXE_LINKER_FLAGS} -lrt" )
message(" .............................. CMAKE_EXE_LINKER_FLAGS ${CMAKE_EXE_LINKER_FLAGS}")


#set(Boost_USE_MULTITHREADED OFF)
#message(" .............................. Boost_USE_MULTITHREADED ${Boost_USE_MULTITHREADED}")






# The following variables are first used as search hints by find modules. 
# If search failed, they are used by the build modules 

# Local configuration
#set (SYMBEX_INSTALL_DIR        /usr/local)

# HIPP (Hudson) configuration
set (SYMBEX_INSTALL_DIR         ${CMAKE_BINARY_DIR}/workswith)


set (SYMBEX_INSTALL_INCLUDE_DIR ${SYMBEX_INSTALL_DIR}/include)
set (SYMBEX_INSTALL_LIB_DIR     ${SYMBEX_INSTALL_DIR}/lib)


set (CVC4_INSTALL_DIR           ${SYMBEX_INSTALL_DIR})
set (CVC4_INSTALL_INCLUDE_DIR   ${SYMBEX_INSTALL_INCLUDE_DIR})
set (CVC4_INSTALL_LIB_DIR       ${SYMBEX_INSTALL_LIB_DIR})

# NOTE: 'antlr2' suffix is automatically added by the configure script
set (ANTLR2_INSTALL_DIR         ${SYMBEX_INSTALL_DIR})
set (ANTLR2_INSTALL_INCLUDE_DIR ${SYMBEX_INSTALL_INCLUDE_DIR})
set (ANTLR2_INSTALL_LIB_DIR     ${SYMBEX_INSTALL_LIB_DIR})

# NOTE: 'antlr3c' suffix is not automatically added by the configure script
set (ANTLR3_INSTALL_DIR         ${SYMBEX_INSTALL_DIR})
set (ANTLR3_INSTALL_INCLUDE_DIR ${SYMBEX_INSTALL_INCLUDE_DIR}/antlr3c)
set (ANTLR3_INSTALL_LIB_DIR     ${SYMBEX_INSTALL_LIB_DIR})


set (BOOST_ROOT /usr) # instead of /usr/local

set (BOOST_INCLUDEDIR           ${BOOST_ROOT}/include/boost)
#set (BOOST_INCLUDE_DIRS        ${BOOST_ROOT}/include)
#set (BOOST_LIBRARYDIR          ${BOOST_ROOT}/lib)
set (BOOST_LIBRARYDIR           /usr/lib/x86_64-linux-gnu/)

#set (BOOST_ROOT                 /home/diversitytest/boost_1_61_0)
#set (BOOST_INCLUDEDIR           /home/diversitytest/boost_1_61_0/boost)
#set (BOOST_LIBRARYDIR           /home/diversitytest/boost_1_61_0/libs)



set (GMP_ROOT /usr)  # instead of /usr/local

set (GMP_INCLUDEDIR ${GMP_ROOT}/include)
set (GMP_LIBRARYDIR ${GMP_ROOT}/lib)

include_directories (${CVC4_INSTALL_INCLUDE_DIR} ${ANTLR2_INSTALL_INCLUDE_DIR} ${ANTLR3_INSTALL_INCLUDE_DIR} ${BOOST_INCLUDEDIR})






