################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/fml/expression/AvmCode.cpp \
../src/fml/expression/AvmCodeFactory.cpp \
../src/fml/expression/BuiltinArray.cpp \
../src/fml/expression/BuiltinContainer.cpp \
../src/fml/expression/BuiltinQueue.cpp \
../src/fml/expression/ExpressionComparer.cpp \
../src/fml/expression/ExpressionConstant.cpp \
../src/fml/expression/ExpressionConstructor.cpp \
../src/fml/expression/ExpressionConstructorImpl.cpp \
../src/fml/expression/ExpressionEval.cpp \
../src/fml/expression/ExpressionFactory.cpp \
../src/fml/expression/ExpressionMapper.cpp \
../src/fml/expression/ExpressionParser.cpp \
../src/fml/expression/ExpressionSimplifier.cpp \
../src/fml/expression/ExpressionTypeChecker.cpp \
../src/fml/expression/StatementConstructor.cpp \
../src/fml/expression/StatementFactory.cpp \
../src/fml/expression/StatementParser.cpp \
../src/fml/expression/StatementTypeChecker.cpp

CPP_DEPS += \
./src/fml/expression/AvmCode.d \
./src/fml/expression/AvmCodeFactory.d \
./src/fml/expression/BuiltinArray.d \
./src/fml/expression/BuiltinContainer.d \
./src/fml/expression/BuiltinQueue.d \
./src/fml/expression/ExpressionComparer.d \
./src/fml/expression/ExpressionConstant.d \
./src/fml/expression/ExpressionConstructor.d \
./src/fml/expression/ExpressionConstructorImpl.d \
./src/fml/expression/ExpressionEval.d \
./src/fml/expression/ExpressionFactory.d \
./src/fml/expression/ExpressionMapper.d \
./src/fml/expression/ExpressionParser.d \
./src/fml/expression/ExpressionSimplifier.d \
./src/fml/expression/ExpressionTypeChecker.d \
./src/fml/expression/StatementConstructor.d \
./src/fml/expression/StatementFactory.d \
./src/fml/expression/StatementParser.d \
./src/fml/expression/StatementTypeChecker.d

OBJS += \
./src/fml/expression/AvmCode.o \
./src/fml/expression/AvmCodeFactory.o \
./src/fml/expression/BuiltinArray.o \
./src/fml/expression/BuiltinContainer.o \
./src/fml/expression/BuiltinQueue.o \
./src/fml/expression/ExpressionComparer.o \
./src/fml/expression/ExpressionConstant.o \
./src/fml/expression/ExpressionConstructor.o \
./src/fml/expression/ExpressionConstructorImpl.o \
./src/fml/expression/ExpressionEval.o \
./src/fml/expression/ExpressionFactory.o \
./src/fml/expression/ExpressionMapper.o \
./src/fml/expression/ExpressionParser.o \
./src/fml/expression/ExpressionSimplifier.o \
./src/fml/expression/ExpressionTypeChecker.o \
./src/fml/expression/StatementConstructor.o \
./src/fml/expression/StatementFactory.o \
./src/fml/expression/StatementParser.o \
./src/fml/expression/StatementTypeChecker.o


# Each subdirectory must supply rules for building sources it contributes
src/fml/expression/%.o: ../src/fml/expression/%.cpp src/fml/expression/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-fml-2f-expression

clean-src-2f-fml-2f-expression:
	-$(RM) ./src/fml/expression/AvmCode.d ./src/fml/expression/AvmCode.o ./src/fml/expression/AvmCodeFactory.d ./src/fml/expression/AvmCodeFactory.o ./src/fml/expression/BuiltinArray.d ./src/fml/expression/BuiltinArray.o ./src/fml/expression/BuiltinContainer.d ./src/fml/expression/BuiltinContainer.o ./src/fml/expression/BuiltinQueue.d ./src/fml/expression/BuiltinQueue.o ./src/fml/expression/ExpressionComparer.d ./src/fml/expression/ExpressionComparer.o ./src/fml/expression/ExpressionConstant.d ./src/fml/expression/ExpressionConstant.o ./src/fml/expression/ExpressionConstructor.d ./src/fml/expression/ExpressionConstructor.o ./src/fml/expression/ExpressionConstructorImpl.d ./src/fml/expression/ExpressionConstructorImpl.o ./src/fml/expression/ExpressionEval.d ./src/fml/expression/ExpressionEval.o ./src/fml/expression/ExpressionFactory.d ./src/fml/expression/ExpressionFactory.o ./src/fml/expression/ExpressionMapper.d ./src/fml/expression/ExpressionMapper.o ./src/fml/expression/ExpressionParser.d ./src/fml/expression/ExpressionParser.o ./src/fml/expression/ExpressionSimplifier.d ./src/fml/expression/ExpressionSimplifier.o ./src/fml/expression/ExpressionTypeChecker.d ./src/fml/expression/ExpressionTypeChecker.o ./src/fml/expression/StatementConstructor.d ./src/fml/expression/StatementConstructor.o ./src/fml/expression/StatementFactory.d ./src/fml/expression/StatementFactory.o ./src/fml/expression/StatementParser.d ./src/fml/expression/StatementParser.o ./src/fml/expression/StatementTypeChecker.d ./src/fml/expression/StatementTypeChecker.o

.PHONY: clean-src-2f-fml-2f-expression

