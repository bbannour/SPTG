# --- Select system specific directives  ---

# Windows/MinGW specific optinos
if ((WIN32) AND (MINGW) AND (MSYS) AND NOT(CYGWIN) AND NOT (UNIX))  # MSYS2 identification by CMake is not really reliable 
    include (SpecificOptions-WinMSYS2) 
elseif ((UNIX) AND NOT (MSYS) AND NOT (CYGWIN)) #  Linux Native
    include (SpecificOptions-Linux)	    
else ()
    message (WARNING "No specific options for the current system")
endif ()
