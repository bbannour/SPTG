################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/builder/primitive/AbstractAvmcodeCompiler.cpp \
../src/builder/primitive/AvmcodeActivityCompiler.cpp \
../src/builder/primitive/AvmcodeAssignCompiler.cpp \
../src/builder/primitive/AvmcodeCommunicationCompiler.cpp \
../src/builder/primitive/AvmcodeCompiler.cpp \
../src/builder/primitive/AvmcodeContainerCompiler.cpp \
../src/builder/primitive/AvmcodeCtorExpressionCompiler.cpp \
../src/builder/primitive/AvmcodeExpressionCompiler.cpp \
../src/builder/primitive/AvmcodeGinacCompiler.cpp \
../src/builder/primitive/AvmcodeGuardCompiler.cpp \
../src/builder/primitive/AvmcodeInvokeCompiler.cpp \
../src/builder/primitive/AvmcodeIteCompiler.cpp \
../src/builder/primitive/AvmcodeJumpCompiler.cpp \
../src/builder/primitive/AvmcodeLambdaCompiler.cpp \
../src/builder/primitive/AvmcodeLookupExprCompiler.cpp \
../src/builder/primitive/AvmcodeLoopCompiler.cpp \
../src/builder/primitive/AvmcodeMachineStatusCompiler.cpp \
../src/builder/primitive/AvmcodeMathFunctionCompiler.cpp \
../src/builder/primitive/AvmcodeMetaStatementCompiler.cpp \
../src/builder/primitive/AvmcodeQueueCompiler.cpp \
../src/builder/primitive/AvmcodeSchedulingCompiler.cpp \
../src/builder/primitive/AvmcodeSequenceCompiler.cpp \
../src/builder/primitive/AvmcodeUfiCastExpressionCompiler.cpp \
../src/builder/primitive/AvmcodeVariableStatusCompiler.cpp \
../src/builder/primitive/CompilationEnvironment.cpp

CPP_DEPS += \
./src/builder/primitive/AbstractAvmcodeCompiler.d \
./src/builder/primitive/AvmcodeActivityCompiler.d \
./src/builder/primitive/AvmcodeAssignCompiler.d \
./src/builder/primitive/AvmcodeCommunicationCompiler.d \
./src/builder/primitive/AvmcodeCompiler.d \
./src/builder/primitive/AvmcodeContainerCompiler.d \
./src/builder/primitive/AvmcodeCtorExpressionCompiler.d \
./src/builder/primitive/AvmcodeExpressionCompiler.d \
./src/builder/primitive/AvmcodeGinacCompiler.d \
./src/builder/primitive/AvmcodeGuardCompiler.d \
./src/builder/primitive/AvmcodeInvokeCompiler.d \
./src/builder/primitive/AvmcodeIteCompiler.d \
./src/builder/primitive/AvmcodeJumpCompiler.d \
./src/builder/primitive/AvmcodeLambdaCompiler.d \
./src/builder/primitive/AvmcodeLookupExprCompiler.d \
./src/builder/primitive/AvmcodeLoopCompiler.d \
./src/builder/primitive/AvmcodeMachineStatusCompiler.d \
./src/builder/primitive/AvmcodeMathFunctionCompiler.d \
./src/builder/primitive/AvmcodeMetaStatementCompiler.d \
./src/builder/primitive/AvmcodeQueueCompiler.d \
./src/builder/primitive/AvmcodeSchedulingCompiler.d \
./src/builder/primitive/AvmcodeSequenceCompiler.d \
./src/builder/primitive/AvmcodeUfiCastExpressionCompiler.d \
./src/builder/primitive/AvmcodeVariableStatusCompiler.d \
./src/builder/primitive/CompilationEnvironment.d

OBJS += \
./src/builder/primitive/AbstractAvmcodeCompiler.o \
./src/builder/primitive/AvmcodeActivityCompiler.o \
./src/builder/primitive/AvmcodeAssignCompiler.o \
./src/builder/primitive/AvmcodeCommunicationCompiler.o \
./src/builder/primitive/AvmcodeCompiler.o \
./src/builder/primitive/AvmcodeContainerCompiler.o \
./src/builder/primitive/AvmcodeCtorExpressionCompiler.o \
./src/builder/primitive/AvmcodeExpressionCompiler.o \
./src/builder/primitive/AvmcodeGinacCompiler.o \
./src/builder/primitive/AvmcodeGuardCompiler.o \
./src/builder/primitive/AvmcodeInvokeCompiler.o \
./src/builder/primitive/AvmcodeIteCompiler.o \
./src/builder/primitive/AvmcodeJumpCompiler.o \
./src/builder/primitive/AvmcodeLambdaCompiler.o \
./src/builder/primitive/AvmcodeLookupExprCompiler.o \
./src/builder/primitive/AvmcodeLoopCompiler.o \
./src/builder/primitive/AvmcodeMachineStatusCompiler.o \
./src/builder/primitive/AvmcodeMathFunctionCompiler.o \
./src/builder/primitive/AvmcodeMetaStatementCompiler.o \
./src/builder/primitive/AvmcodeQueueCompiler.o \
./src/builder/primitive/AvmcodeSchedulingCompiler.o \
./src/builder/primitive/AvmcodeSequenceCompiler.o \
./src/builder/primitive/AvmcodeUfiCastExpressionCompiler.o \
./src/builder/primitive/AvmcodeVariableStatusCompiler.o \
./src/builder/primitive/CompilationEnvironment.o


# Each subdirectory must supply rules for building sources it contributes
src/builder/primitive/%.o: ../src/builder/primitive/%.cpp src/builder/primitive/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-builder-2f-primitive

clean-src-2f-builder-2f-primitive:
	-$(RM) ./src/builder/primitive/AbstractAvmcodeCompiler.d ./src/builder/primitive/AbstractAvmcodeCompiler.o ./src/builder/primitive/AvmcodeActivityCompiler.d ./src/builder/primitive/AvmcodeActivityCompiler.o ./src/builder/primitive/AvmcodeAssignCompiler.d ./src/builder/primitive/AvmcodeAssignCompiler.o ./src/builder/primitive/AvmcodeCommunicationCompiler.d ./src/builder/primitive/AvmcodeCommunicationCompiler.o ./src/builder/primitive/AvmcodeCompiler.d ./src/builder/primitive/AvmcodeCompiler.o ./src/builder/primitive/AvmcodeContainerCompiler.d ./src/builder/primitive/AvmcodeContainerCompiler.o ./src/builder/primitive/AvmcodeCtorExpressionCompiler.d ./src/builder/primitive/AvmcodeCtorExpressionCompiler.o ./src/builder/primitive/AvmcodeExpressionCompiler.d ./src/builder/primitive/AvmcodeExpressionCompiler.o ./src/builder/primitive/AvmcodeGinacCompiler.d ./src/builder/primitive/AvmcodeGinacCompiler.o ./src/builder/primitive/AvmcodeGuardCompiler.d ./src/builder/primitive/AvmcodeGuardCompiler.o ./src/builder/primitive/AvmcodeInvokeCompiler.d ./src/builder/primitive/AvmcodeInvokeCompiler.o ./src/builder/primitive/AvmcodeIteCompiler.d ./src/builder/primitive/AvmcodeIteCompiler.o ./src/builder/primitive/AvmcodeJumpCompiler.d ./src/builder/primitive/AvmcodeJumpCompiler.o ./src/builder/primitive/AvmcodeLambdaCompiler.d ./src/builder/primitive/AvmcodeLambdaCompiler.o ./src/builder/primitive/AvmcodeLookupExprCompiler.d ./src/builder/primitive/AvmcodeLookupExprCompiler.o ./src/builder/primitive/AvmcodeLoopCompiler.d ./src/builder/primitive/AvmcodeLoopCompiler.o ./src/builder/primitive/AvmcodeMachineStatusCompiler.d ./src/builder/primitive/AvmcodeMachineStatusCompiler.o ./src/builder/primitive/AvmcodeMathFunctionCompiler.d ./src/builder/primitive/AvmcodeMathFunctionCompiler.o ./src/builder/primitive/AvmcodeMetaStatementCompiler.d ./src/builder/primitive/AvmcodeMetaStatementCompiler.o ./src/builder/primitive/AvmcodeQueueCompiler.d ./src/builder/primitive/AvmcodeQueueCompiler.o ./src/builder/primitive/AvmcodeSchedulingCompiler.d ./src/builder/primitive/AvmcodeSchedulingCompiler.o ./src/builder/primitive/AvmcodeSequenceCompiler.d ./src/builder/primitive/AvmcodeSequenceCompiler.o ./src/builder/primitive/AvmcodeUfiCastExpressionCompiler.d ./src/builder/primitive/AvmcodeUfiCastExpressionCompiler.o ./src/builder/primitive/AvmcodeVariableStatusCompiler.d ./src/builder/primitive/AvmcodeVariableStatusCompiler.o ./src/builder/primitive/CompilationEnvironment.d ./src/builder/primitive/CompilationEnvironment.o

.PHONY: clean-src-2f-builder-2f-primitive

