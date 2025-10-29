################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/solver/api/SatSolver.cpp \
../src/solver/api/SolverDef.cpp \
../src/solver/api/SolverFactory.cpp

CPP_DEPS += \
./src/solver/api/SatSolver.d \
./src/solver/api/SolverDef.d \
./src/solver/api/SolverFactory.d

OBJS += \
./src/solver/api/SatSolver.o \
./src/solver/api/SolverDef.o \
./src/solver/api/SolverFactory.o


# Each subdirectory must supply rules for building sources it contributes
src/solver/api/%.o: ../src/solver/api/%.cpp src/solver/api/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-solver-2f-api

clean-src-2f-solver-2f-api:
	-$(RM) ./src/solver/api/SatSolver.d ./src/solver/api/SatSolver.o ./src/solver/api/SolverDef.d ./src/solver/api/SolverDef.o ./src/solver/api/SolverFactory.d ./src/solver/api/SolverFactory.o

.PHONY: clean-src-2f-solver-2f-api

