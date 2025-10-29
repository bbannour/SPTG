################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/famsc/FamSystemComplianceExposer.cpp

CPP_DEPS += \
./src/famsc/FamSystemComplianceExposer.d

OBJS += \
./src/famsc/FamSystemComplianceExposer.o


# Each subdirectory must supply rules for building sources it contributes
src/famsc/%.o: ../src/famsc/%.cpp src/famsc/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-famsc

clean-src-2f-famsc:
	-$(RM) ./src/famsc/FamSystemComplianceExposer.d ./src/famsc/FamSystemComplianceExposer.o

.PHONY: clean-src-2f-famsc

