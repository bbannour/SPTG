# PENDING : TO BE CONTINUED

message ("Build GMP from sources ...")
set (GMP_URL https://gmplib.org/repo/gmp-6.1)
set (GMP_DOS2UNIX sh -c "dos2unix.exe *")
set (GMP_CONFIGURE sh configure)
set (GMP_CONFIGURE ${GMP_CONFIGURE} --enable-cxx --disable-shared)
set (GMP_CONFIGURE ${GMP_CONFIGURE} CC=${CMAKE_C_COMPILER} CXX=${CMAKE_CXX_COMPILER})
# configure --enable-cxx --disable-shared CC=C:/MinGW/bin/gcc.exe CXX=C:/MinGW/bin/g++.exe

externalproject_add (gmp
                      SOURCE_DIR ${CMAKE_CURRENT_SOURCE_DIR}/gmp
                      HG_REPOSITORY ${GMP_URL}
                      CONFIGURE_COMMAND  ${GMP_DOS2UNIX} COMMAND sh ./.bootstrap COMMAND ${GMP_CONFIGURE}
                      BUILD_COMMAND make
                      BUILD_IN_SOURCE 1)