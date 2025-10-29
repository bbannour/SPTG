################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/builder/analysis/CommunicationDependency.cpp \
../src/builder/analysis/MachineDependency.cpp \
../src/builder/analysis/TransitionReachability.cpp

CPP_DEPS += \
./src/builder/analysis/CommunicationDependency.d \
./src/builder/analysis/MachineDependency.d \
./src/builder/analysis/TransitionReachability.d

OBJS += \
./src/builder/analysis/CommunicationDependency.o \
./src/builder/analysis/MachineDependency.o \
./src/builder/analysis/TransitionReachability.o


# Each subdirectory must supply rules for building sources it contributes
src/builder/analysis/%.o: ../src/builder/analysis/%.cpp src/builder/analysis/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-builder-2f-analysis

clean-src-2f-builder-2f-analysis:
	-$(RM) ./src/builder/analysis/CommunicationDependency.d ./src/builder/analysis/CommunicationDependency.o ./src/builder/analysis/MachineDependency.d ./src/builder/analysis/MachineDependency.o ./src/builder/analysis/TransitionReachability.d ./src/builder/analysis/TransitionReachability.o

.PHONY: clean-src-2f-builder-2f-analysis

