# =============================================================================
#               CMake module building ANTLR2 from sources
# =============================================================================


include (ExternalProject)

set (ANTLR277_DIR antlr-2.7.7)
set (ANTLR277_ARC ${ANTLR277_DIR}.tar.gz)
set (ANTLR277_URL http://www.antlr2.org/download/${ANTLR277_ARC})


if (NOT (DEFINED ANTLR2_INSTALL_DIR))
#    set (ANTLR2_INSTALL_DIR /home/lapitre_is148245/efm/symbex_hipp/org.eclipse.efm-symbex/org.eclipse.efm.symbex/build_gui/contrib)
    set (ANTLR2_INSTALL_DIR ${CMAKE_BINARY_DIR}/contrib)
    set (ANTLR2_INSTALL_LIB_DIR ${ANTLR2_INSTALL_DIR}/lib)
    set (ANTLR2_INSTALL_INCLUDE_DIR ${ANTLR2_INSTALL_DIR}/include)
    
    MESSAGE( ANTLR2_INSTALL_DIR: ${ANTLR2_INSTALL_DIR})
    MESSAGE( ANTLR2_INSTALL_LIB_DIR: ${ANTLR2_INSTALL_LIB_DIR})
    MESSAGE( ANTLR2_INSTALL_INCLUDE_DIR:  ${ANTLR2_INSTALL_INCLUDE_DIR})
endif()

set (ANTLR2_CONFIGURE                     configure)
set (ANTLR2_CONFIGURE ${ANTLR2_CONFIGURE} --prefix=${ANTLR2_INSTALL_DIR})
# Fine tunning of installation directories
#set (ANTLR2_CONFIGURE ${ANTLR2_CONFIGURE} --libdir=${ANTLR2_INSTALL_LIB_DIR} --includedir=${ANTLR2_INSTALL_INCLUDE_DIR})


externalproject_add (antlr2
    
    # Download step
    DOWNLOAD_DIR      ${CMAKE_BINARY_DIR}
    URL               ${ANTLR277_URL}
    PREFIX            antlr2
    
    # Patch step
    PATCH_COMMAND     ${CMAKE_COMMAND} -E copy ${CMAKE_SOURCE_DIR}/cmake/antlr2-patch/lib/cpp/antlr/CharScanner.hpp ${CMAKE_BINARY_DIR}/antlr2/src/antlr2/lib/cpp/antlr
          COMMAND     ${CMAKE_COMMAND} -E copy ${CMAKE_SOURCE_DIR}/cmake/antlr2-patch/scripts/config.guess ${CMAKE_BINARY_DIR}/antlr2/src/antlr2/scripts
          COMMAND     ${CMAKE_COMMAND} -E copy ${CMAKE_SOURCE_DIR}/cmake/antlr2-patch/scripts/config.sub ${CMAKE_BINARY_DIR}/antlr2/src/antlr2/scripts
    
    # Configure step
    CONFIGURE_COMMAND ${CMAKE_BINARY_DIR}/antlr2/src/antlr2/${ANTLR2_CONFIGURE}

    # Build step
    BUILD_COMMAND     make 
    
    # Install step
    INSTALL_COMMAND   make install
    )

# These variables ca be used by the client code of this module (ex: FindModule)
set (ANTLR2_INCLUDE_DIR ${ANTLR2_INSTALL_INCLUDE_DIR})
set (ANTLR2_LIBRARIES   libantlr.a) 
