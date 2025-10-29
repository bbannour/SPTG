################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/solver/Z3Solver.cpp \
../src/solver/Z3_C_Solver.cpp

CPP_DEPS += \
./src/solver/Z3Solver.d \
./src/solver/Z3_C_Solver.d

OBJS += \
./src/solver/Z3Solver.o \
./src/solver/Z3_C_Solver.o


# Each subdirectory must supply rules for building sources it contributes
src/solver/%.o: ../src/solver/%.cpp src/solver/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-solver

clean-src-2f-solver:
	-$(RM) ./src/solver/Z3Solver.d ./src/solver/Z3Solver.o ./src/solver/Z3_C_Solver.d ./src/solver/Z3_C_Solver.o

.PHONY: clean-src-2f-solver

