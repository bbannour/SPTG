################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/fml/lib/AvmAnalysis.cpp \
../src/fml/lib/AvmLang.cpp \
../src/fml/lib/AvmOperationExpression.cpp \
../src/fml/lib/AvmOperationFactory.cpp \
../src/fml/lib/AvmOperationMachine.cpp \
../src/fml/lib/AvmOperationVariable.cpp \
../src/fml/lib/IComPoint.cpp \
../src/fml/lib/ITracePoint.cpp \
../src/fml/lib/ITypeSpecifier.cpp

CPP_DEPS += \
./src/fml/lib/AvmAnalysis.d \
./src/fml/lib/AvmLang.d \
./src/fml/lib/AvmOperationExpression.d \
./src/fml/lib/AvmOperationFactory.d \
./src/fml/lib/AvmOperationMachine.d \
./src/fml/lib/AvmOperationVariable.d \
./src/fml/lib/IComPoint.d \
./src/fml/lib/ITracePoint.d \
./src/fml/lib/ITypeSpecifier.d

OBJS += \
./src/fml/lib/AvmAnalysis.o \
./src/fml/lib/AvmLang.o \
./src/fml/lib/AvmOperationExpression.o \
./src/fml/lib/AvmOperationFactory.o \
./src/fml/lib/AvmOperationMachine.o \
./src/fml/lib/AvmOperationVariable.o \
./src/fml/lib/IComPoint.o \
./src/fml/lib/ITracePoint.o \
./src/fml/lib/ITypeSpecifier.o


# Each subdirectory must supply rules for building sources it contributes
src/fml/lib/%.o: ../src/fml/lib/%.cpp src/fml/lib/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-fml-2f-lib

clean-src-2f-fml-2f-lib:
	-$(RM) ./src/fml/lib/AvmAnalysis.d ./src/fml/lib/AvmAnalysis.o ./src/fml/lib/AvmLang.d ./src/fml/lib/AvmLang.o ./src/fml/lib/AvmOperationExpression.d ./src/fml/lib/AvmOperationExpression.o ./src/fml/lib/AvmOperationFactory.d ./src/fml/lib/AvmOperationFactory.o ./src/fml/lib/AvmOperationMachine.d ./src/fml/lib/AvmOperationMachine.o ./src/fml/lib/AvmOperationVariable.d ./src/fml/lib/AvmOperationVariable.o ./src/fml/lib/IComPoint.d ./src/fml/lib/IComPoint.o ./src/fml/lib/ITracePoint.d ./src/fml/lib/ITracePoint.o ./src/fml/lib/ITypeSpecifier.d ./src/fml/lib/ITypeSpecifier.o

.PHONY: clean-src-2f-fml-2f-lib

