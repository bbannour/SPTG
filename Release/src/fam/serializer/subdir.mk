################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/fam/serializer/GraphicExecutionSequenceSerializer.cpp

CPP_DEPS += \
./src/fam/serializer/GraphicExecutionSequenceSerializer.d

OBJS += \
./src/fam/serializer/GraphicExecutionSequenceSerializer.o


# Each subdirectory must supply rules for building sources it contributes
src/fam/serializer/%.o: ../src/fam/serializer/%.cpp src/fam/serializer/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++-12 -pipe -std=c++17 -D__AVM_LINUX__ -D_GIT_VERSION_=\"$(shell git describe --always --tags)\" -DEXPERIMENTAL_FEATURE -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_OMEGA_ -D_AVM_SOLVER_CVC4_ -D_AVM_SOLVER_CVC5_ -D_AVM_SOLVER_Z3_C_ -D_AVM_SOLVER_YICES_V2_ -U_AVM_BUILTIN_NUMERIC_BOOST_ -I"/home/al203168/_myWorks_/git/intra/org.eclipse.efm-symbex/org.eclipse.efm.symbex/src" -I"/home/al203168/_myWorks_/git/intra/org.eclipse.efm-symbex/org.eclipse.efm.symbex/third-party/include" -I"/home/al203168/_myWorks_/git/intra/org.eclipse.efm-symbex/org.eclipse.efm.symbex/third-party/include/omega" -I"/home/al203168/_myWorks_/git/intra/org.eclipse.efm-symbex/org.eclipse.efm.symbex/third-party/include/antlr4-runtime" -O0 -g3 -Wall -c -fmessage-length=0 -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-fam-2f-serializer

clean-src-2f-fam-2f-serializer:
	-$(RM) ./src/fam/serializer/GraphicExecutionSequenceSerializer.d ./src/fam/serializer/GraphicExecutionSequenceSerializer.o

.PHONY: clean-src-2f-fam-2f-serializer

