# =============================================================================
#              CMake module: Setup of Windows/MSYS2 specific options
# =============================================================================
#
#  Note: Set here only options that cannot be declared at general level 
#        (i. e. that are platform dependant)
#        This is also the right place to define hints to search for
#        prerequisites
#
#  Note: We assume a 64 bits built, which implies the use of 
#        /msys64/mingw64 directory for install.
#
#  Warning: Use Windows style paths not MSYS2 path !
#
# =============================================================================



# ===================== Compilation level options ==============================
set (WINMSYS2_FLAGS -D__AVM_MINGW__ -D__AVM_WINDOWS__)
set (WINMSYS2_OPTS -fmessage-length=0 -pipe -std=c++17 )
add_definitions     (${WINMSYS2_FLAGS})
add_compile_options (${WINMSYS2_OPTS})


# =========================== Link level options ===============================
set (CMAKE_EXE_LINKER_FLAGS ${CMAKE_EXE_LINKER_FLAGS}) # None
# TODO : use add_link_option when goign to cmake >= 3.13

# ================== Library Position Independent Code suffix ==================
set (PIC_SUFFIX  )



# === TODO TODO TODO : set the right hint path from a MSYS2 install ===

# ============================== Search hints ==================================
# You can add (or remove) locations according to your needs
# For example: 

# ANTLR3C
set (ANTLR3C_INSTALL_INCLUDE_DIR  /c/msys64/mingw64/include)
set (ANTLR3C_INSTALL_LIB_DIR      /c/msys64/mingw64/lib)

# ANTLR4
set (ANTLR4_INSTALL_INCLUDE_DIR   /c/msys64/mingw64/include/antlr4-runtime)
set (ANTLR4_INSTALL_LIB_DIR       /c/msys64/mingw64/lib)

# CVC4
set (CVC4_INSTALL_INCLUDE_DIR     /c/msys64/mingw64/include)
set (CVC4_INSTALL_LIB_DIR         /c/msys64/mingw64/lib)

# Z3
set (Z3_INSTALL_INCLUDE_DIR       /c/msys64/mingw64/include)
set (Z3_INSTALL_LIB_DIR           /c/msys64/mingw64/lib)

# Yices2
set (Yices2_INSTALL_INCLUDE_DIR   /c/msys64/mingw64/include)
set (Yices2_INSTALL_LIB_DIR       /c/msys64/mingw64/lib)

# BOOST
set (Boost_INSTALL_INCLUDE_DIR    /c/msys64/mingw64/include)
set (Boost_INSTALL_LIB_DIR        /c/msys64/mingw64/lib)
set (Boost_LIB_PYTHON3            python38)

# GMP
set (GMP_INSTALL_INCLUDE_DIR      /c/msys64/mingw64/include)
set (GMP_INSTALL_LIB_DIR          /c/msys64/mingw64/lib)

# GMPXX
set (GMP_INSTALL_INCLUDE_DIR      /c/msys64/mingw64/include)
set (GMP_INSTALL_LIB_DIR          /c/msys64/mingw64/lib)


# TO BE REVIEWED : USEFUL ?
# HIPP (Hudson) configuration
set (SYMBEX_INSTALL_DIR         ${CMAKE_BINARY_DIR}/workswith)
#set (SYMBEX_INSTALL_DIR        /usr/local)

set (SYMBEX_INSTALL_INCLUDE_DIR ${SYMBEX_INSTALL_DIR}/include)
set (SYMBEX_INSTALL_LIB_DIR     ${SYMBEX_INSTALL_DIR}/lib)
set (ENV{JAVAC}                       "/c/Program\\\ Files")
message(STATUS "The specific ENV value of JAVAC: " $ENV{JAVAC})


message (STATUS "Current compiler flags: ${WINMSYS2_FLAGS}")
message (STATUS "Current compiler options: ${WINMSYS2_OPTS}")
message (STATUS "Current Linker options: ${CMAKE_EXE_LINKER_FLAGS}")


message (STATUS)




