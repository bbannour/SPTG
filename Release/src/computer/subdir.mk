################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/computer/BaseEnvironment.cpp \
../src/computer/EnvironmentFactory.cpp \
../src/computer/EvaluationEnvironment.cpp \
../src/computer/ExecutionDataFactory.cpp \
../src/computer/ExecutionEnvironment.cpp \
../src/computer/PathConditionProcessor.cpp

CPP_DEPS += \
./src/computer/BaseEnvironment.d \
./src/computer/EnvironmentFactory.d \
./src/computer/EvaluationEnvironment.d \
./src/computer/ExecutionDataFactory.d \
./src/computer/ExecutionEnvironment.d \
./src/computer/PathConditionProcessor.d

OBJS += \
./src/computer/BaseEnvironment.o \
./src/computer/EnvironmentFactory.o \
./src/computer/EvaluationEnvironment.o \
./src/computer/ExecutionDataFactory.o \
./src/computer/ExecutionEnvironment.o \
./src/computer/PathConditionProcessor.o


# Each subdirectory must supply rules for building sources it contributes
src/computer/%.o: ../src/computer/%.cpp src/computer/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-computer

clean-src-2f-computer:
	-$(RM) ./src/computer/BaseEnvironment.d ./src/computer/BaseEnvironment.o ./src/computer/EnvironmentFactory.d ./src/computer/EnvironmentFactory.o ./src/computer/EvaluationEnvironment.d ./src/computer/EvaluationEnvironment.o ./src/computer/ExecutionDataFactory.d ./src/computer/ExecutionDataFactory.o ./src/computer/ExecutionEnvironment.d ./src/computer/ExecutionEnvironment.o ./src/computer/PathConditionProcessor.d ./src/computer/PathConditionProcessor.o

.PHONY: clean-src-2f-computer

