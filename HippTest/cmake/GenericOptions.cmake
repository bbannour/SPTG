# =============================================================================
#               CMake file for generic built options
# =============================================================================
#
# Note : These compile directives propagate to all targets on all systems
#
# =============================================================================


# What is defined 
#add_definitions (-D_AVM_BUILT_WITH_CMAKE_ -D_AVM_SOLVER_CVC4_ -D_AVM_BUILTIN_NUMERIC_BOOST_)
add_definitions (-D_AVM_BUILT_WITH_CMAKE_ -D_AVM_SOLVER_CVC4_ -D_AVM_BUILTIN_NUMERIC_GMP_)


# What is undefined
add_definitions (-U_AVM_SOLVER_YICES_V1_ -U_AVM_SOLVER_YICES_V2_ -U_AVM_SOLVER_CVC3_ -U _AVM_EXPRESSION_GINAC_ -U_AVM_SOLVER_OMEGA_)
add_definitions(-U_AVM_BUILTIN_NUMERIC_BOOST_)


