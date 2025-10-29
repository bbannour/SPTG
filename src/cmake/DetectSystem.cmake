# =============================================================================
#       CMake module: getting properties of the current platform
# =============================================================================


include(Utils)


formatprint (100 "=" "" "" " Looking for: system info ")


# Endianness testing (answer in variable SYSTEM_IS_BIG_ENDIAN)
include (TestBigEndian)
test_big_endian (SYSTEM_IS_BIG_ENDIAN)
if (SYSTEM_IS_BIG_ENDIAN)
  set (SYSTEM_IS_BIG_ENDIAN_STR Yes)
else()
	set (SYSTEM_IS_BIG_ENDIAN_STR No)
endif()

# Processors testing (answer in variable SYSTEM_PROCESSOR_COUNT)
include (ProcessorCount)
ProcessorCount (SYSTEM_PROCESSOR_COUNT)

# Checking type size (result in bytes)
include (CheckTypeSize)
check_type_size (char SIZEOF_CHAR LANGUAGE CXX)
check_type_size (short SIZEOF_SHORT_INT LANGUAGE CXX)
check_type_size (int SIZEOF_INT LANGUAGE CXX)
check_type_size (long SIZEOF_LONG_INT LANGUAGE CXX)
check_type_size ("long long" SIZEOF_LONG_LONG_INT LANGUAGE CXX)
check_type_size (float SIZEOF_FLOAT LANGUAGE CXX)
check_type_size (double SIZEOF_DOUBLE LANGUAGE CXX)

# Report
message (STATUS "System            : ${CMAKE_SYSTEM}-${CMAKE_SYSTEM_PROCESSOR}")
message (STATUS "System (CMake var): WIN32=${WIN32}  MINGW=${MINGW} UNIX=${UNIX} MSYS=${MSYS} CYGWIN=${CYGWIN}")
message (STATUS "Big-endian        : ${SYSTEM_IS_BIG_ENDIAN_STR}")
message (STATUS "Types size (bytes): char=${SIZEOF_CHAR} short=${SIZEOF_SHORT_INT} int=${SIZEOF_INT} long=${SIZEOF_LONG_INT} 'long long'=${SIZEOF_LONG_LONG_INT} float=${SIZEOF_FLOAT} double=${SIZEOF_DOUBLE}")
message (STATUS "Processor count   : ${SYSTEM_PROCESSOR_COUNT}")
message (STATUS)
