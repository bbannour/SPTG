################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/computer/primitive/AvmActivityPrimitive.cpp \
../src/computer/primitive/AvmAssignPrimitive.cpp \
../src/computer/primitive/AvmBaseConcurrencyPrimitive.cpp \
../src/computer/primitive/AvmBitwisePrimitive.cpp \
../src/computer/primitive/AvmBufferPrimitive.cpp \
../src/computer/primitive/AvmCommunicationFactory.cpp \
../src/computer/primitive/AvmCommunicationPrimitive.cpp \
../src/computer/primitive/AvmCommunicationRdvPrimitive.cpp \
../src/computer/primitive/AvmConcurrencyPrimitive.cpp \
../src/computer/primitive/AvmCtorPrimitive.cpp \
../src/computer/primitive/AvmExpressionPrimitive.cpp \
../src/computer/primitive/AvmGuardPrimitive.cpp \
../src/computer/primitive/AvmInputEnabledPrimitive.cpp \
../src/computer/primitive/AvmInvokePrimitive.cpp \
../src/computer/primitive/AvmItePrimitive.cpp \
../src/computer/primitive/AvmIterationPrimitive.cpp \
../src/computer/primitive/AvmJumpPrimitive.cpp \
../src/computer/primitive/AvmLookupPrimitive.cpp \
../src/computer/primitive/AvmMathPrimitive.cpp \
../src/computer/primitive/AvmMetaPrimitive.cpp \
../src/computer/primitive/AvmPrimitiveProcessor.cpp \
../src/computer/primitive/AvmSchedulingPrimitive.cpp \
../src/computer/primitive/AvmSequencePrimitive.cpp \
../src/computer/primitive/AvmStatusPrimitive.cpp \
../src/computer/primitive/AvmSynchronizationFactory.cpp \
../src/computer/primitive/BaseAvmPrimitive.cpp

CPP_DEPS += \
./src/computer/primitive/AvmActivityPrimitive.d \
./src/computer/primitive/AvmAssignPrimitive.d \
./src/computer/primitive/AvmBaseConcurrencyPrimitive.d \
./src/computer/primitive/AvmBitwisePrimitive.d \
./src/computer/primitive/AvmBufferPrimitive.d \
./src/computer/primitive/AvmCommunicationFactory.d \
./src/computer/primitive/AvmCommunicationPrimitive.d \
./src/computer/primitive/AvmCommunicationRdvPrimitive.d \
./src/computer/primitive/AvmConcurrencyPrimitive.d \
./src/computer/primitive/AvmCtorPrimitive.d \
./src/computer/primitive/AvmExpressionPrimitive.d \
./src/computer/primitive/AvmGuardPrimitive.d \
./src/computer/primitive/AvmInputEnabledPrimitive.d \
./src/computer/primitive/AvmInvokePrimitive.d \
./src/computer/primitive/AvmItePrimitive.d \
./src/computer/primitive/AvmIterationPrimitive.d \
./src/computer/primitive/AvmJumpPrimitive.d \
./src/computer/primitive/AvmLookupPrimitive.d \
./src/computer/primitive/AvmMathPrimitive.d \
./src/computer/primitive/AvmMetaPrimitive.d \
./src/computer/primitive/AvmPrimitiveProcessor.d \
./src/computer/primitive/AvmSchedulingPrimitive.d \
./src/computer/primitive/AvmSequencePrimitive.d \
./src/computer/primitive/AvmStatusPrimitive.d \
./src/computer/primitive/AvmSynchronizationFactory.d \
./src/computer/primitive/BaseAvmPrimitive.d

OBJS += \
./src/computer/primitive/AvmActivityPrimitive.o \
./src/computer/primitive/AvmAssignPrimitive.o \
./src/computer/primitive/AvmBaseConcurrencyPrimitive.o \
./src/computer/primitive/AvmBitwisePrimitive.o \
./src/computer/primitive/AvmBufferPrimitive.o \
./src/computer/primitive/AvmCommunicationFactory.o \
./src/computer/primitive/AvmCommunicationPrimitive.o \
./src/computer/primitive/AvmCommunicationRdvPrimitive.o \
./src/computer/primitive/AvmConcurrencyPrimitive.o \
./src/computer/primitive/AvmCtorPrimitive.o \
./src/computer/primitive/AvmExpressionPrimitive.o \
./src/computer/primitive/AvmGuardPrimitive.o \
./src/computer/primitive/AvmInputEnabledPrimitive.o \
./src/computer/primitive/AvmInvokePrimitive.o \
./src/computer/primitive/AvmItePrimitive.o \
./src/computer/primitive/AvmIterationPrimitive.o \
./src/computer/primitive/AvmJumpPrimitive.o \
./src/computer/primitive/AvmLookupPrimitive.o \
./src/computer/primitive/AvmMathPrimitive.o \
./src/computer/primitive/AvmMetaPrimitive.o \
./src/computer/primitive/AvmPrimitiveProcessor.o \
./src/computer/primitive/AvmSchedulingPrimitive.o \
./src/computer/primitive/AvmSequencePrimitive.o \
./src/computer/primitive/AvmStatusPrimitive.o \
./src/computer/primitive/AvmSynchronizationFactory.o \
./src/computer/primitive/BaseAvmPrimitive.o


# Each subdirectory must supply rules for building sources it contributes
src/computer/primitive/%.o: ../src/computer/primitive/%.cpp src/computer/primitive/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-computer-2f-primitive

clean-src-2f-computer-2f-primitive:
	-$(RM) ./src/computer/primitive/AvmActivityPrimitive.d ./src/computer/primitive/AvmActivityPrimitive.o ./src/computer/primitive/AvmAssignPrimitive.d ./src/computer/primitive/AvmAssignPrimitive.o ./src/computer/primitive/AvmBaseConcurrencyPrimitive.d ./src/computer/primitive/AvmBaseConcurrencyPrimitive.o ./src/computer/primitive/AvmBitwisePrimitive.d ./src/computer/primitive/AvmBitwisePrimitive.o ./src/computer/primitive/AvmBufferPrimitive.d ./src/computer/primitive/AvmBufferPrimitive.o ./src/computer/primitive/AvmCommunicationFactory.d ./src/computer/primitive/AvmCommunicationFactory.o ./src/computer/primitive/AvmCommunicationPrimitive.d ./src/computer/primitive/AvmCommunicationPrimitive.o ./src/computer/primitive/AvmCommunicationRdvPrimitive.d ./src/computer/primitive/AvmCommunicationRdvPrimitive.o ./src/computer/primitive/AvmConcurrencyPrimitive.d ./src/computer/primitive/AvmConcurrencyPrimitive.o ./src/computer/primitive/AvmCtorPrimitive.d ./src/computer/primitive/AvmCtorPrimitive.o ./src/computer/primitive/AvmExpressionPrimitive.d ./src/computer/primitive/AvmExpressionPrimitive.o ./src/computer/primitive/AvmGuardPrimitive.d ./src/computer/primitive/AvmGuardPrimitive.o ./src/computer/primitive/AvmInputEnabledPrimitive.d ./src/computer/primitive/AvmInputEnabledPrimitive.o ./src/computer/primitive/AvmInvokePrimitive.d ./src/computer/primitive/AvmInvokePrimitive.o ./src/computer/primitive/AvmItePrimitive.d ./src/computer/primitive/AvmItePrimitive.o ./src/computer/primitive/AvmIterationPrimitive.d ./src/computer/primitive/AvmIterationPrimitive.o ./src/computer/primitive/AvmJumpPrimitive.d ./src/computer/primitive/AvmJumpPrimitive.o ./src/computer/primitive/AvmLookupPrimitive.d ./src/computer/primitive/AvmLookupPrimitive.o ./src/computer/primitive/AvmMathPrimitive.d ./src/computer/primitive/AvmMathPrimitive.o ./src/computer/primitive/AvmMetaPrimitive.d ./src/computer/primitive/AvmMetaPrimitive.o ./src/computer/primitive/AvmPrimitiveProcessor.d ./src/computer/primitive/AvmPrimitiveProcessor.o ./src/computer/primitive/AvmSchedulingPrimitive.d ./src/computer/primitive/AvmSchedulingPrimitive.o ./src/computer/primitive/AvmSequencePrimitive.d ./src/computer/primitive/AvmSequencePrimitive.o ./src/computer/primitive/AvmStatusPrimitive.d ./src/computer/primitive/AvmStatusPrimitive.o ./src/computer/primitive/AvmSynchronizationFactory.d ./src/computer/primitive/AvmSynchronizationFactory.o ./src/computer/primitive/BaseAvmPrimitive.d ./src/computer/primitive/BaseAvmPrimitive.o

.PHONY: clean-src-2f-computer-2f-primitive

