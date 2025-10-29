################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/computer/instruction/InstructionEnvironment.cpp

CPP_DEPS += \
./src/computer/instruction/InstructionEnvironment.d

OBJS += \
./src/computer/instruction/InstructionEnvironment.o


# Each subdirectory must supply rules for building sources it contributes
src/computer/instruction/%.o: ../src/computer/instruction/%.cpp src/computer/instruction/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-computer-2f-instruction

clean-src-2f-computer-2f-instruction:
	-$(RM) ./src/computer/instruction/InstructionEnvironment.d ./src/computer/instruction/InstructionEnvironment.o

.PHONY: clean-src-2f-computer-2f-instruction

