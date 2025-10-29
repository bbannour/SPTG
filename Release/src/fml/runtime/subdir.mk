################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/fml/runtime/ExecutionConfiguration.cpp \
../src/fml/runtime/ExecutionContext.cpp \
../src/fml/runtime/ExecutionContextFlags.cpp \
../src/fml/runtime/ExecutionData.cpp \
../src/fml/runtime/ExecutionInformation.cpp \
../src/fml/runtime/ExecutionLocation.cpp \
../src/fml/runtime/ExecutionSynchronizationPoint.cpp \
../src/fml/runtime/LocalRuntime.cpp \
../src/fml/runtime/Message.cpp \
../src/fml/runtime/RuntimeDef.cpp \
../src/fml/runtime/RuntimeForm.cpp \
../src/fml/runtime/RuntimeID.cpp \
../src/fml/runtime/RuntimeLib.cpp \
../src/fml/runtime/RuntimeQuery.cpp \
../src/fml/runtime/TableOfData.cpp \
../src/fml/runtime/TableOfRuntimeFormState.cpp

CPP_DEPS += \
./src/fml/runtime/ExecutionConfiguration.d \
./src/fml/runtime/ExecutionContext.d \
./src/fml/runtime/ExecutionContextFlags.d \
./src/fml/runtime/ExecutionData.d \
./src/fml/runtime/ExecutionInformation.d \
./src/fml/runtime/ExecutionLocation.d \
./src/fml/runtime/ExecutionSynchronizationPoint.d \
./src/fml/runtime/LocalRuntime.d \
./src/fml/runtime/Message.d \
./src/fml/runtime/RuntimeDef.d \
./src/fml/runtime/RuntimeForm.d \
./src/fml/runtime/RuntimeID.d \
./src/fml/runtime/RuntimeLib.d \
./src/fml/runtime/RuntimeQuery.d \
./src/fml/runtime/TableOfData.d \
./src/fml/runtime/TableOfRuntimeFormState.d

OBJS += \
./src/fml/runtime/ExecutionConfiguration.o \
./src/fml/runtime/ExecutionContext.o \
./src/fml/runtime/ExecutionContextFlags.o \
./src/fml/runtime/ExecutionData.o \
./src/fml/runtime/ExecutionInformation.o \
./src/fml/runtime/ExecutionLocation.o \
./src/fml/runtime/ExecutionSynchronizationPoint.o \
./src/fml/runtime/LocalRuntime.o \
./src/fml/runtime/Message.o \
./src/fml/runtime/RuntimeDef.o \
./src/fml/runtime/RuntimeForm.o \
./src/fml/runtime/RuntimeID.o \
./src/fml/runtime/RuntimeLib.o \
./src/fml/runtime/RuntimeQuery.o \
./src/fml/runtime/TableOfData.o \
./src/fml/runtime/TableOfRuntimeFormState.o


# Each subdirectory must supply rules for building sources it contributes
src/fml/runtime/%.o: ../src/fml/runtime/%.cpp src/fml/runtime/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-fml-2f-runtime

clean-src-2f-fml-2f-runtime:
	-$(RM) ./src/fml/runtime/ExecutionConfiguration.d ./src/fml/runtime/ExecutionConfiguration.o ./src/fml/runtime/ExecutionContext.d ./src/fml/runtime/ExecutionContext.o ./src/fml/runtime/ExecutionContextFlags.d ./src/fml/runtime/ExecutionContextFlags.o ./src/fml/runtime/ExecutionData.d ./src/fml/runtime/ExecutionData.o ./src/fml/runtime/ExecutionInformation.d ./src/fml/runtime/ExecutionInformation.o ./src/fml/runtime/ExecutionLocation.d ./src/fml/runtime/ExecutionLocation.o ./src/fml/runtime/ExecutionSynchronizationPoint.d ./src/fml/runtime/ExecutionSynchronizationPoint.o ./src/fml/runtime/LocalRuntime.d ./src/fml/runtime/LocalRuntime.o ./src/fml/runtime/Message.d ./src/fml/runtime/Message.o ./src/fml/runtime/RuntimeDef.d ./src/fml/runtime/RuntimeDef.o ./src/fml/runtime/RuntimeForm.d ./src/fml/runtime/RuntimeForm.o ./src/fml/runtime/RuntimeID.d ./src/fml/runtime/RuntimeID.o ./src/fml/runtime/RuntimeLib.d ./src/fml/runtime/RuntimeLib.o ./src/fml/runtime/RuntimeQuery.d ./src/fml/runtime/RuntimeQuery.o ./src/fml/runtime/TableOfData.d ./src/fml/runtime/TableOfData.o ./src/fml/runtime/TableOfRuntimeFormState.d ./src/fml/runtime/TableOfRuntimeFormState.o

.PHONY: clean-src-2f-fml-2f-runtime

