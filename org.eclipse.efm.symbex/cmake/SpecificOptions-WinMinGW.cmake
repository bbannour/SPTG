# --- Setup of Windows/MinGW specific options ---

message ("Setting specific options for Windows/MinGW...")

# Compilation directives
add_definitions (-D__AVM_MINGW__ -D__AVM_WINDOWS__)
add_compile_options (-fmessage-length=0 -pipe)

# Prerequisites default localization
if (NOT BOOST_ROOT)
    set (BOOST_ROOT C:/boost-1.53)
endif ()

if (NOT GMP_ROOT)
  set (GMP_ROOT C:/GMP)
endif ()

if (NOT ANTLR_ROOT)
  set (ANTLR_ROOT C:/ANTLR)
endif ()

if (NOT CVC4_ROOT)
  set (CVC4_ROOT C:/CVC4)
endif ()

if (NOT OMEGA_ROOT)
  set (OMEGA_ROOT C:/Omega)
endif ()
