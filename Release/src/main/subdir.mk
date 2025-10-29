################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/main/AvmLauncher.cpp \
../src/main/AvmMain.cpp \
../src/main/FamExposer.cpp \
../src/main/SignalHandler.cpp \
../src/main/StaticInitializer.cpp \
../src/main/main.cpp

CPP_DEPS += \
./src/main/AvmLauncher.d \
./src/main/AvmMain.d \
./src/main/FamExposer.d \
./src/main/SignalHandler.d \
./src/main/StaticInitializer.d \
./src/main/main.d

OBJS += \
./src/main/AvmLauncher.o \
./src/main/AvmMain.o \
./src/main/FamExposer.o \
./src/main/SignalHandler.o \
./src/main/StaticInitializer.o \
./src/main/main.o


# Each subdirectory must supply rules for building sources it contributes
src/main/%.o: ../src/main/%.cpp src/main/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-main

clean-src-2f-main:
	-$(RM) ./src/main/AvmLauncher.d ./src/main/AvmLauncher.o ./src/main/AvmMain.d ./src/main/AvmMain.o ./src/main/FamExposer.d ./src/main/FamExposer.o ./src/main/SignalHandler.d ./src/main/SignalHandler.o ./src/main/StaticInitializer.d ./src/main/StaticInitializer.o ./src/main/main.d ./src/main/main.o

.PHONY: clean-src-2f-main

