# ==============================================================================
#                 CMake module: Select system specific options
# ==============================================================================
#
# Remark : OS specific options should propagate to all subtargets. Hence this
#          file must be included in the main CMakeFile.txt before project 
#          structure is defined
# ==============================================================================



include(Utils)


# Windows/MinGW
if ((WIN32) AND (MINGW) AND (MSYS) AND NOT(CYGWIN) AND NOT (UNIX)) # MSYS2 identification by CMake is not really reliable 
  
  formatprint (100 "=" "" "" " Platform options for: Windows MSYS2 ")
  include (PlatformOptions-WinMSYS2)

# Linux Native
elseif ((UNIX) AND NOT (MSYS) AND NOT (CYGWIN)) 
  
  formatprint (100 "=" "" "" " Platform options for: Linux ")
  include (PlatformOptions-Linux)	    

else ()
  
  message (WARNING "No specific options for the current system")

endif ()
