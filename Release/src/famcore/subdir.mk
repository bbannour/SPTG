################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/famcore/FamCoreExposer.cpp \
../src/famcore/FormulaCoverageFilter.cpp \
../src/famcore/StatemachineReachability.cpp

CPP_DEPS += \
./src/famcore/FamCoreExposer.d \
./src/famcore/FormulaCoverageFilter.d \
./src/famcore/StatemachineReachability.d

OBJS += \
./src/famcore/FamCoreExposer.o \
./src/famcore/FormulaCoverageFilter.o \
./src/famcore/StatemachineReachability.o


# Each subdirectory must supply rules for building sources it contributes
src/famcore/%.o: ../src/famcore/%.cpp src/famcore/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-famcore

clean-src-2f-famcore:
	-$(RM) ./src/famcore/FamCoreExposer.d ./src/famcore/FamCoreExposer.o ./src/famcore/FormulaCoverageFilter.d ./src/famcore/FormulaCoverageFilter.o ./src/famcore/StatemachineReachability.d ./src/famcore/StatemachineReachability.o

.PHONY: clean-src-2f-famcore

