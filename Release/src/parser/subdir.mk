################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/parser/Antlr4ErrorFactory.cpp \
../src/parser/ParserManager.cpp \
../src/parser/ParserUtil.cpp

CPP_DEPS += \
./src/parser/Antlr4ErrorFactory.d \
./src/parser/ParserManager.d \
./src/parser/ParserUtil.d

OBJS += \
./src/parser/Antlr4ErrorFactory.o \
./src/parser/ParserManager.o \
./src/parser/ParserUtil.o


# Each subdirectory must supply rules for building sources it contributes
src/parser/%.o: ../src/parser/%.cpp src/parser/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-parser

clean-src-2f-parser:
	-$(RM) ./src/parser/Antlr4ErrorFactory.d ./src/parser/Antlr4ErrorFactory.o ./src/parser/ParserManager.d ./src/parser/ParserManager.o ./src/parser/ParserUtil.d ./src/parser/ParserUtil.o

.PHONY: clean-src-2f-parser

