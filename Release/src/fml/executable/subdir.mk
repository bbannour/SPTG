################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/fml/executable/AvmBytecode.cpp \
../src/fml/executable/AvmInstruction.cpp \
../src/fml/executable/AvmLambda.cpp \
../src/fml/executable/AvmProgram.cpp \
../src/fml/executable/AvmTransition.cpp \
../src/fml/executable/BaseAvmProgram.cpp \
../src/fml/executable/BaseCompiledForm.cpp \
../src/fml/executable/BaseInstanceForm.cpp \
../src/fml/executable/ExecutableForm.cpp \
../src/fml/executable/ExecutableLib.cpp \
../src/fml/executable/ExecutableQuery.cpp \
../src/fml/executable/ExecutableSystem.cpp \
../src/fml/executable/InstanceOfBuffer.cpp \
../src/fml/executable/InstanceOfConnector.cpp \
../src/fml/executable/InstanceOfData.cpp \
../src/fml/executable/InstanceOfMachine.cpp \
../src/fml/executable/InstanceOfPort.cpp \
../src/fml/executable/Router.cpp \
../src/fml/executable/RoutingData.cpp

CPP_DEPS += \
./src/fml/executable/AvmBytecode.d \
./src/fml/executable/AvmInstruction.d \
./src/fml/executable/AvmLambda.d \
./src/fml/executable/AvmProgram.d \
./src/fml/executable/AvmTransition.d \
./src/fml/executable/BaseAvmProgram.d \
./src/fml/executable/BaseCompiledForm.d \
./src/fml/executable/BaseInstanceForm.d \
./src/fml/executable/ExecutableForm.d \
./src/fml/executable/ExecutableLib.d \
./src/fml/executable/ExecutableQuery.d \
./src/fml/executable/ExecutableSystem.d \
./src/fml/executable/InstanceOfBuffer.d \
./src/fml/executable/InstanceOfConnector.d \
./src/fml/executable/InstanceOfData.d \
./src/fml/executable/InstanceOfMachine.d \
./src/fml/executable/InstanceOfPort.d \
./src/fml/executable/Router.d \
./src/fml/executable/RoutingData.d

OBJS += \
./src/fml/executable/AvmBytecode.o \
./src/fml/executable/AvmInstruction.o \
./src/fml/executable/AvmLambda.o \
./src/fml/executable/AvmProgram.o \
./src/fml/executable/AvmTransition.o \
./src/fml/executable/BaseAvmProgram.o \
./src/fml/executable/BaseCompiledForm.o \
./src/fml/executable/BaseInstanceForm.o \
./src/fml/executable/ExecutableForm.o \
./src/fml/executable/ExecutableLib.o \
./src/fml/executable/ExecutableQuery.o \
./src/fml/executable/ExecutableSystem.o \
./src/fml/executable/InstanceOfBuffer.o \
./src/fml/executable/InstanceOfConnector.o \
./src/fml/executable/InstanceOfData.o \
./src/fml/executable/InstanceOfMachine.o \
./src/fml/executable/InstanceOfPort.o \
./src/fml/executable/Router.o \
./src/fml/executable/RoutingData.o


# Each subdirectory must supply rules for building sources it contributes
src/fml/executable/%.o: ../src/fml/executable/%.cpp src/fml/executable/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-fml-2f-executable

clean-src-2f-fml-2f-executable:
	-$(RM) ./src/fml/executable/AvmBytecode.d ./src/fml/executable/AvmBytecode.o ./src/fml/executable/AvmInstruction.d ./src/fml/executable/AvmInstruction.o ./src/fml/executable/AvmLambda.d ./src/fml/executable/AvmLambda.o ./src/fml/executable/AvmProgram.d ./src/fml/executable/AvmProgram.o ./src/fml/executable/AvmTransition.d ./src/fml/executable/AvmTransition.o ./src/fml/executable/BaseAvmProgram.d ./src/fml/executable/BaseAvmProgram.o ./src/fml/executable/BaseCompiledForm.d ./src/fml/executable/BaseCompiledForm.o ./src/fml/executable/BaseInstanceForm.d ./src/fml/executable/BaseInstanceForm.o ./src/fml/executable/ExecutableForm.d ./src/fml/executable/ExecutableForm.o ./src/fml/executable/ExecutableLib.d ./src/fml/executable/ExecutableLib.o ./src/fml/executable/ExecutableQuery.d ./src/fml/executable/ExecutableQuery.o ./src/fml/executable/ExecutableSystem.d ./src/fml/executable/ExecutableSystem.o ./src/fml/executable/InstanceOfBuffer.d ./src/fml/executable/InstanceOfBuffer.o ./src/fml/executable/InstanceOfConnector.d ./src/fml/executable/InstanceOfConnector.o ./src/fml/executable/InstanceOfData.d ./src/fml/executable/InstanceOfData.o ./src/fml/executable/InstanceOfMachine.d ./src/fml/executable/InstanceOfMachine.o ./src/fml/executable/InstanceOfPort.d ./src/fml/executable/InstanceOfPort.o ./src/fml/executable/Router.d ./src/fml/executable/Router.o ./src/fml/executable/RoutingData.d ./src/fml/executable/RoutingData.o

.PHONY: clean-src-2f-fml-2f-executable

