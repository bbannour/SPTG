# ==============================================================================
#               CMake module: Setup of Native Linux specific options
# ==============================================================================
#
#  Note: Set here only options that cannot be declared at general level 
#        (i. e. that are platform dependant)
#        This is also the right place to define hints to search for
#        prerequisites
#
# ==============================================================================



# ===================== Compilation level options ==============================
set (LINUX_FLAGS -D__AVM_UNIX__ -D__AVM_LINUX__)
set (LINUX_OPTS -fmessage-length=0 -pipe  -fPIC -fpermissive)
add_definitions     (${LINUX_FLAGS})
add_compile_options (${LINUX_OPTS})


# =========================== Link level options ===============================
set (CMAKE_EXE_LINKER_FLAGS ${CMAKE_EXE_LINKER_FLAGS} -lrt)
# TODO : use add_link_option when goign to cmake >= 3.13

# ================== Library Position Independent Code suffix ==================
set (PIC_SUFFIX    -pic)

# ============================== Search hints ==================================
# You can add (or remove) locations according to your needs

# ANTLR3C
set (ANTLR3C_INSTALL_INCLUDE_DIR  /usr/include)
set (ANTLR3C_INSTALL_LIB_DIR      /usr/lib /usr/lib/x86_64-linux-gnu)

# ANTLR4
set (ANTLR4_INSTALL_INCLUDE_DIR   /usr/include/antlr4-runtime)
set (ANTLR4_INSTALL_LIB_DIR       /usr/lib/)

# CVC4
set (CVC4_INSTALL_INCLUDE_DIR     /usr/include)
set (CVC4_INSTALL_LIB_DIR         /usr/lib)

# Z3
set (Z3_INSTALL_INCLUDE_DIR       /usr/include)
set (Z3_INSTALL_LIB_DIR           /usr/lib/x86_64-linux-gnu)

# Yices2
set (Yices2_INSTALL_INCLUDE_DIR   /usr/local/include)
set (Yices2_INSTALL_LIB_DIR       /usr/local/lib)

# BOOST
set (Boost_INSTALL_INCLUDE_DIR    /usr/include/boost ${BOOST_ROOT}/include/boost)
set (Boost_INSTALL_LIB_DIR        /usr/lib/x86_64-linux-gnu ${BOOST_ROOT}/lib)
set (Boost_LIB_PYTHON3            python)

# GMP
set (GMP_INSTALL_INCLUDE_DIR      /usr/include/x86_64-linux-gnu)
set (GMP_INSTALL_LIB_DIR          /usr/lib/x86_64-linux-gnu)

# GMPXX
set (GMP_INSTALL_INCLUDE_DIR      /usr/include)
set (GMP_INSTALL_LIB_DIR          /usr/lib/x86_64-linux-gnu)


# TO BE REVIEWED : USEFUL ?
# HIPP (Hudson) configuration
set (SYMBEX_INSTALL_DIR         ${CMAKE_BINARY_DIR}/workswith)
#set (SYMBEX_INSTALL_DIR        /usr/local)

set (SYMBEX_INSTALL_INCLUDE_DIR ${SYMBEX_INSTALL_DIR}/include)
set (SYMBEX_INSTALL_LIB_DIR     ${SYMBEX_INSTALL_DIR}/lib)

message (STATUS "Current compiler flags: ${LINUX_FLAGS}")
message (STATUS "Current compiler options: ${LINUX_OPTS}")
message (STATUS "Current Linker options: ${CMAKE_EXE_LINKER_FLAGS}")


message (STATUS)
