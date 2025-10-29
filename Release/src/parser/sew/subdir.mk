################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/parser/sew/SEWLexer.cpp \
../src/parser/sew/SEWParser.cpp

CPP_DEPS += \
./src/parser/sew/SEWLexer.d \
./src/parser/sew/SEWParser.d

OBJS += \
./src/parser/sew/SEWLexer.o \
./src/parser/sew/SEWParser.o


# Each subdirectory must supply rules for building sources it contributes
src/parser/sew/%.o: ../src/parser/sew/%.cpp src/parser/sew/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-parser-2f-sew

clean-src-2f-parser-2f-sew:
	-$(RM) ./src/parser/sew/SEWLexer.d ./src/parser/sew/SEWLexer.o ./src/parser/sew/SEWParser.d ./src/parser/sew/SEWParser.o

.PHONY: clean-src-2f-parser-2f-sew

