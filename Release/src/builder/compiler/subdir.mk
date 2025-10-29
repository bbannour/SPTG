################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/builder/compiler/BaseCompiler.cpp \
../src/builder/compiler/BaseMachineCompiler.cpp \
../src/builder/compiler/Compiler.cpp \
../src/builder/compiler/CompilerOfInteraction.cpp \
../src/builder/compiler/CompilerOfTransition.cpp \
../src/builder/compiler/CompilerOfVariable.cpp \
../src/builder/compiler/SymbolTable.cpp

CPP_DEPS += \
./src/builder/compiler/BaseCompiler.d \
./src/builder/compiler/BaseMachineCompiler.d \
./src/builder/compiler/Compiler.d \
./src/builder/compiler/CompilerOfInteraction.d \
./src/builder/compiler/CompilerOfTransition.d \
./src/builder/compiler/CompilerOfVariable.d \
./src/builder/compiler/SymbolTable.d

OBJS += \
./src/builder/compiler/BaseCompiler.o \
./src/builder/compiler/BaseMachineCompiler.o \
./src/builder/compiler/Compiler.o \
./src/builder/compiler/CompilerOfInteraction.o \
./src/builder/compiler/CompilerOfTransition.o \
./src/builder/compiler/CompilerOfVariable.o \
./src/builder/compiler/SymbolTable.o


# Each subdirectory must supply rules for building sources it contributes
src/builder/compiler/%.o: ../src/builder/compiler/%.cpp src/builder/compiler/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-builder-2f-compiler

clean-src-2f-builder-2f-compiler:
	-$(RM) ./src/builder/compiler/BaseCompiler.d ./src/builder/compiler/BaseCompiler.o ./src/builder/compiler/BaseMachineCompiler.d ./src/builder/compiler/BaseMachineCompiler.o ./src/builder/compiler/Compiler.d ./src/builder/compiler/Compiler.o ./src/builder/compiler/CompilerOfInteraction.d ./src/builder/compiler/CompilerOfInteraction.o ./src/builder/compiler/CompilerOfTransition.d ./src/builder/compiler/CompilerOfTransition.o ./src/builder/compiler/CompilerOfVariable.d ./src/builder/compiler/CompilerOfVariable.o ./src/builder/compiler/SymbolTable.d ./src/builder/compiler/SymbolTable.o

.PHONY: clean-src-2f-builder-2f-compiler

