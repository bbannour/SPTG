################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/famcore/debug/AvmDebugProcessor.cpp \
../src/famcore/debug/IDebugProcessorHelper.cpp \
../src/famcore/debug/IDebugProcessorProvider.cpp

CPP_DEPS += \
./src/famcore/debug/AvmDebugProcessor.d \
./src/famcore/debug/IDebugProcessorHelper.d \
./src/famcore/debug/IDebugProcessorProvider.d

OBJS += \
./src/famcore/debug/AvmDebugProcessor.o \
./src/famcore/debug/IDebugProcessorHelper.o \
./src/famcore/debug/IDebugProcessorProvider.o


# Each subdirectory must supply rules for building sources it contributes
src/famcore/debug/%.o: ../src/famcore/debug/%.cpp src/famcore/debug/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-famcore-2f-debug

clean-src-2f-famcore-2f-debug:
	-$(RM) ./src/famcore/debug/AvmDebugProcessor.d ./src/famcore/debug/AvmDebugProcessor.o ./src/famcore/debug/IDebugProcessorHelper.d ./src/famcore/debug/IDebugProcessorHelper.o ./src/famcore/debug/IDebugProcessorProvider.d ./src/famcore/debug/IDebugProcessorProvider.o

.PHONY: clean-src-2f-famcore-2f-debug

