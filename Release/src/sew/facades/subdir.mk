################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/sew/facades/Py_Engine.cpp \
../src/sew/facades/Py_Result.cpp \
../src/sew/facades/Py_WorkflowParameter.cpp

OBJS += \
./src/sew/facades/Py_Engine.o \
./src/sew/facades/Py_Result.o \
./src/sew/facades/Py_WorkflowParameter.o

CPP_DEPS += \
./src/sew/facades/Py_Engine.d \
./src/sew/facades/Py_Result.d \
./src/sew/facades/Py_WorkflowParameter.d


# Each subdirectory must supply rules for building sources it contributes
src/sew/facades/%.o: ../src/sew/facades/%.cpp src/sew/facades/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++-10 -pipe -std=c++17 -D__AVM_LINUX__ -D_GIT_VERSION_=\"$(shell git describe --always --tags)\" -DEXPERIMENTAL_FEATURE -D_ANTLR4_ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_OMEGA_ -D_AVM_SOLVER_CVC4_ -D_AVM_SOLVER_Z3_C_ -D_AVM_SOLVER_YICES_V2_ -U_AVM_BUILTIN_NUMERIC_BOOST_ -I"/home/al203168/_myWorks_/git/intra/org.eclipse.efm-symbex/org.eclipse.efm.symbex/src" -I"/home/al203168/_myWorks_/git/intra/org.eclipse.efm-symbex/org.eclipse.efm.symbex/third-party/include" -I"/home/al203168/_myWorks_/git/intra/org.eclipse.efm-symbex/org.eclipse.efm.symbex/third-party/include/omega" -I/usr/include/antlr4-runtime -O0 -g3 -Wall -c -fmessage-length=0 -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


