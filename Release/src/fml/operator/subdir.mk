################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/fml/operator/Operator.cpp \
../src/fml/operator/OperatorLib.cpp \
../src/fml/operator/OperatorManager.cpp

CPP_DEPS += \
./src/fml/operator/Operator.d \
./src/fml/operator/OperatorLib.d \
./src/fml/operator/OperatorManager.d

OBJS += \
./src/fml/operator/Operator.o \
./src/fml/operator/OperatorLib.o \
./src/fml/operator/OperatorManager.o


# Each subdirectory must supply rules for building sources it contributes
src/fml/operator/%.o: ../src/fml/operator/%.cpp src/fml/operator/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-fml-2f-operator

clean-src-2f-fml-2f-operator:
	-$(RM) ./src/fml/operator/Operator.d ./src/fml/operator/Operator.o ./src/fml/operator/OperatorLib.d ./src/fml/operator/OperatorLib.o ./src/fml/operator/OperatorManager.d ./src/fml/operator/OperatorManager.o

.PHONY: clean-src-2f-fml-2f-operator

