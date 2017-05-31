# ===============================================================================
#           CMake module : Search for mandatory prerequisites 
# ===============================================================================
# 
# This module looks for mandatory libraries and sets variable 
# like <XXX>_LIBRARIES and <XXX>_INCLUDE_DIR
# Variables of the form <XXX>_ROOT are passed to the Find modules which use them as hints
#
# ===============================================================================


message (STATUS "****** Looking for mandatory prerequisites ******")

# ---------------------------- Looking for Boost ------------------------------
#
# Variable BOOST_ROOT is used as a search hint by find_package
#
message (STATUS "**** Looking for BOOST ****")

set (Boost_DEBUG ON) # Enable boost DEBUG


# BOOST_COMPONENTS should contains the required boost components  
set (Boost_USE_STATIC_LIBS ON) # Force to lookg for static libraries
find_package (Boost 1.40 REQUIRED COMPONENTS ${BOOST_COMPONENTS})
if (NOT (Boost_FOUND)) 
    message (FATAL_ERROR "Boost not found : please install Boost >= 1.53 manually")
else ()
    message (STATUS "Boost : " ${Boost_LIBRARIES} "-" ${Boost_INCLUDE_DIRS} "-" ${Boost_LIBRARY_DIRS})
endif()
message (STATUS "****                   ****")

# --------------------------- Looking for GPM ---------------------------------
# 
# The GMP_ROOT variable is used as a search hint
# 
message (STATUS "****  Looking for GMP  ****")
find_package(GMP 6.1.0 REQUIRED)
if (NOT (GMP_FOUND))
    message (FATAL_ERROR "GMP not found : please install GMP  >= 6.1.0 manually")
else ()
    message (STATUS "GMP : " ${lib_gmp_c} "-" ${lib_gmp_cxx} "-" ${gmp_includedir} "-" ${gmpxx_includedir})
endif()
message (STATUS "****                   ****")

# --------------------------- Looking for CVC4 --------------------------------
#
# CVC4_INSTALL_INCLUDE_DIR : hint to find includes
# CVC4_INSTALL_LIB_DIR     : hint to find libraries 
#
find_package(CVC4)
if (NOT (CVC4_FOUND))  
    message("CVC4 not found : later, I will try to build CVC4 from sources (including an ANTLR3 build)")
    include (BuildCVC4)
    add_custom_target (rescan_cvc4 ${CMAKE_COMMAND} ${CMAKE_SOURCE_DIR} DEPENDS cvc4)
else ()
    add_custom_target (rescan_cvc4)
endif()


# -------------------------- Looking for ANTLR2 -------------------------------
#
# ANTLR2_INSTALL_INCLUDE_DIR : hint to find includes
# ANTLR2_INSTALL_LIB_DIR     : hint to find libraries
#
find_package(ANTLR2)
if (NOT (ANTLR2_FOUND))
    message ("ANTLR2 not found : later, I will try to build ANTLR2 from sources")
    include (BuildANTLR2)
    add_custom_target (rescan_antlr2 ${CMAKE_COMMAND} ${CMAKE_SOURCE_DIR} DEPENDS antlr2 )
else ()
    add_custom_target (rescan_antlr2)
endif()


# -------------------- Looking for ANTLR3 C runtime ---------------------------
# The ANTLR3_INSTALL_INCLUDE_DIR and ANTLR3_INSTALL_LIB_DIR variables are used as search hints
find_package(ANTLR3)
if (NOT (ANTLR3_FOUND))
    message ("ANTLR3 not found : please install ANTLR3 package manually or (re)install CVC4 (which comes with an automatic ANTLR3 installation)")
endif()


