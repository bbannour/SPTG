# =============================================================================
#       CMake module getting some properties from the current platform
# =============================================================================


message (STATUS "****** Looking for system information ******")

# Endianness testing (answer in variable SYSTEM_IS_BIG_ENDIAN)
include (TestBigEndian)
test_big_endian (SYSTEM_IS_BIG_ENDIAN)
if (SYSTEM_IS_BIG_ENDIAN)
	set (SYSTEM_IS_BIG_ENDIAN_STR Yes)
else ()
	set (SYSTEM_IS_BIG_ENDIAN_STR No)
endif ()

# Processors testing (answer in variable SYSTEM_NB_OF_PROC)
include (ProcessorCount)
ProcessorCount (SYSTEM_NB_OF_PROC)

# Checking type size (result in bytes)
include (CheckTypeSize)
check_type_size (int INT_SIZE LANGUAGE CXX)
check_type_size (short SHORT_INT_SIZE LANGUAGE CXX)
check_type_size (long LONG_INT_SIZE LANGUAGE CXX)
check_type_size (char CHAR_SIZE LANGUAGE CXX)

# Report
message (STATUS "System            : ${CMAKE_SYSTEM}-${CMAKE_SYSTEM_PROCESSOR}")
message (STATUS "System (CMake var): WIN32=${WIN32}  MINGW=${MINGW} UNIX=${UNIX} MSYS=${MSYS} CYGWIN=${CYGWIN}")
message (STATUS "Big-endian        : ${SYSTEM_IS_BIG_ENDIAN_STR}")
message (STATUS "Types size (bytes): int=${INT_SIZE}  shortint=${SHORT_INT_SIZE}  longint=${LONG_INT_SIZE} char=${CHAR_SIZE}")
message (STATUS "Nb of processors  : ${SYSTEM_NB_OF_PROC}")

