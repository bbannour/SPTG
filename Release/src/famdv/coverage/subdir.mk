################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/famdv/coverage/AvmCoverageAbstractView.cpp \
../src/famdv/coverage/AvmCoverageDirectiveTraceBuilder.cpp \
../src/famdv/coverage/AvmCoverageOneTraceDriver.cpp \
../src/famdv/coverage/AvmCoverageProcessor.cpp \
../src/famdv/coverage/AvmCoverageTraceDriver.cpp \
../src/famdv/coverage/AvmCoverageTraceView.cpp \
../src/famdv/coverage/AvmCoverageTransitionView.cpp \
../src/famdv/coverage/MachineCoverageFilter.cpp \
../src/famdv/coverage/TransitionCoverageFilter.cpp

CPP_DEPS += \
./src/famdv/coverage/AvmCoverageAbstractView.d \
./src/famdv/coverage/AvmCoverageDirectiveTraceBuilder.d \
./src/famdv/coverage/AvmCoverageOneTraceDriver.d \
./src/famdv/coverage/AvmCoverageProcessor.d \
./src/famdv/coverage/AvmCoverageTraceDriver.d \
./src/famdv/coverage/AvmCoverageTraceView.d \
./src/famdv/coverage/AvmCoverageTransitionView.d \
./src/famdv/coverage/MachineCoverageFilter.d \
./src/famdv/coverage/TransitionCoverageFilter.d

OBJS += \
./src/famdv/coverage/AvmCoverageAbstractView.o \
./src/famdv/coverage/AvmCoverageDirectiveTraceBuilder.o \
./src/famdv/coverage/AvmCoverageOneTraceDriver.o \
./src/famdv/coverage/AvmCoverageProcessor.o \
./src/famdv/coverage/AvmCoverageTraceDriver.o \
./src/famdv/coverage/AvmCoverageTraceView.o \
./src/famdv/coverage/AvmCoverageTransitionView.o \
./src/famdv/coverage/MachineCoverageFilter.o \
./src/famdv/coverage/TransitionCoverageFilter.o


# Each subdirectory must supply rules for building sources it contributes
src/famdv/coverage/%.o: ../src/famdv/coverage/%.cpp src/famdv/coverage/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-famdv-2f-coverage

clean-src-2f-famdv-2f-coverage:
	-$(RM) ./src/famdv/coverage/AvmCoverageAbstractView.d ./src/famdv/coverage/AvmCoverageAbstractView.o ./src/famdv/coverage/AvmCoverageDirectiveTraceBuilder.d ./src/famdv/coverage/AvmCoverageDirectiveTraceBuilder.o ./src/famdv/coverage/AvmCoverageOneTraceDriver.d ./src/famdv/coverage/AvmCoverageOneTraceDriver.o ./src/famdv/coverage/AvmCoverageProcessor.d ./src/famdv/coverage/AvmCoverageProcessor.o ./src/famdv/coverage/AvmCoverageTraceDriver.d ./src/famdv/coverage/AvmCoverageTraceDriver.o ./src/famdv/coverage/AvmCoverageTraceView.d ./src/famdv/coverage/AvmCoverageTraceView.o ./src/famdv/coverage/AvmCoverageTransitionView.d ./src/famdv/coverage/AvmCoverageTransitionView.o ./src/famdv/coverage/MachineCoverageFilter.d ./src/famdv/coverage/MachineCoverageFilter.o ./src/famdv/coverage/TransitionCoverageFilter.d ./src/famdv/coverage/TransitionCoverageFilter.o

.PHONY: clean-src-2f-famdv-2f-coverage

