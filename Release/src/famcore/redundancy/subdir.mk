################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/famcore/redundancy/BaseDataComparator.cpp \
../src/famcore/redundancy/ConfigurationComparator.cpp \
../src/famcore/redundancy/DataSolverComparator.cpp \
../src/famcore/redundancy/DataSyntaxicEquivalence.cpp \
../src/famcore/redundancy/RedundancyFilter.cpp

CPP_DEPS += \
./src/famcore/redundancy/BaseDataComparator.d \
./src/famcore/redundancy/ConfigurationComparator.d \
./src/famcore/redundancy/DataSolverComparator.d \
./src/famcore/redundancy/DataSyntaxicEquivalence.d \
./src/famcore/redundancy/RedundancyFilter.d

OBJS += \
./src/famcore/redundancy/BaseDataComparator.o \
./src/famcore/redundancy/ConfigurationComparator.o \
./src/famcore/redundancy/DataSolverComparator.o \
./src/famcore/redundancy/DataSyntaxicEquivalence.o \
./src/famcore/redundancy/RedundancyFilter.o


# Each subdirectory must supply rules for building sources it contributes
src/famcore/redundancy/%.o: ../src/famcore/redundancy/%.cpp src/famcore/redundancy/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-famcore-2f-redundancy

clean-src-2f-famcore-2f-redundancy:
	-$(RM) ./src/famcore/redundancy/BaseDataComparator.d ./src/famcore/redundancy/BaseDataComparator.o ./src/famcore/redundancy/ConfigurationComparator.d ./src/famcore/redundancy/ConfigurationComparator.o ./src/famcore/redundancy/DataSolverComparator.d ./src/famcore/redundancy/DataSolverComparator.o ./src/famcore/redundancy/DataSyntaxicEquivalence.d ./src/famcore/redundancy/DataSyntaxicEquivalence.o ./src/famcore/redundancy/RedundancyFilter.d ./src/famcore/redundancy/RedundancyFilter.o

.PHONY: clean-src-2f-famcore-2f-redundancy

