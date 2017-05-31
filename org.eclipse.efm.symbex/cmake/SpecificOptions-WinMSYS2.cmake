# =============================================================================
#                   Setup of Windows/MSYS2 specific options
# =============================================================================
#
# Note : We assume a 64 bits built, which implies the use of 
#        /msys64/mingw64 directory for install.
#
# Warning : Use Windows style paths not MSYS2 path !
#
# =============================================================================


message (STATUS "****** Setting options for Windows/MSYS2 ******")

# Compilation directives
add_definitions     (-D__AVM_MINGW__ -D__AVM_WINDOWS__)
add_compile_options (-fmessage-length=0 -pipe)

# The following variables are first used as search hints by find modules. 
# If search failed, they are used by the build modules (as configure scripts
# of the prerequisites know nothing about MSYS2, we need to force them to use
# the MSYS2 install directories)

set (CVC4_INSTALL_INCLUDE_DIR   C:/msys64/mingw64/usr/include)
set (CVC4_INSTALL_LIB_DIR       C:/msys64/mingw64/usr/lib)

# NOTE: 'antlr' suffix is automatically added by the configure script
set (ANTLR2_INSTALL_INCLUDE_DIR C:/msys64/mingw64/usr/include)
set (ANTLR2_INSTALL_LIB_DIR     C:/msys64/mingw64/usr/lib)

set (ANTLR3_INSTALL_INCLUDE_DIR C:/msys64/mingw64/usr/include)
set (ANTLR3_INSTALL_LIB_DIR     C:/msys64/mingw64/usr/lib)

# FIXME : use of .../mingw642 instead of .../mingw64 is compulsory due to a CVC4 configure bug
set (BOOST_ROOT                 C:/msys64/mingw642) 
set (BOOST_INCLUDEDIR           C:/msys64/mingw642/include) # FIXME 
set (BOOST_LIBRARYDIR           C:/msys64/mingw642/include/lib) # FIXME 

set (GMP_ROOT C:/msys64/mingw64)
set (GMP_INCLUDEDIR C:/msys64/mingw64/include)
set (GMP_LIBRARYDIR C:/msys64/mingw64/lib)



include_directories (${CVC4_INSTALL_INCLUDE_DIR} ${ANTLR2_INSTALL_INCLUDE_DIR} ${ANTLR3_INSTALL_INCLUDE_DIR})

# FIXME : Temporary bypass for the 'CVC4/configure/boost/mingw64' bug on MSYS2
set (Boost_INCLUDE_DIRS /mingw642/include)
set (Boost_LIBRARY_DIRS /mingw642/lib)
# End FIXME
