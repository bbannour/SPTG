################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/famcore/serializer/facades/Py_Display.cpp

CPP_DEPS += \
./src/famcore/serializer/facades/Py_Display.d

OBJS += \
./src/famcore/serializer/facades/Py_Display.o


# Each subdirectory must supply rules for building sources it contributes
src/famcore/serializer/facades/%.o: ../src/famcore/serializer/facades/%.cpp src/famcore/serializer/facades/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++-14 -pipe -std=c++2a -D__AVM_LINUX__ -D_GIT_VERSION_=\"$(shell git describe --always --tags)\" -DEXPERIMENTAL_FEATURE -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -D_AVM_SOLVER_CVC5_ -D_AVM_SOLVER_YICES_V2_ -U_AVM_BUILTIN_NUMERIC_BOOST_ -U_AVM_SOLVER_OMEGA_ -U_AVM_SOLVER_CVC4_ -I"/home/al203168/_myWorks_/git/intra/org.eclipse.efm-symbex/org.eclipse.efm.symbex/src" -I"/home/al203168/_myWorks_/git/intra/org.eclipse.efm-symbex/org.eclipse.efm.symbex/third-party/include" -I"/home/al203168/_myWorks_/git/intra/org.eclipse.efm-symbex/org.eclipse.efm.symbex/third-party/include/omega" -I"/home/al203168/_myWorks_/git/intra/org.eclipse.efm-symbex/org.eclipse.efm.symbex/third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-famcore-2f-serializer-2f-facades

clean-src-2f-famcore-2f-serializer-2f-facades:
	-$(RM) ./src/famcore/serializer/facades/Py_Display.d ./src/famcore/serializer/facades/Py_Display.o

.PHONY: clean-src-2f-famcore-2f-serializer-2f-facades

