################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/printer/Manipulators.cpp \
../src/printer/OutStream.cpp \
../src/printer/WrapStream.cpp

CPP_DEPS += \
./src/printer/Manipulators.d \
./src/printer/OutStream.d \
./src/printer/WrapStream.d

OBJS += \
./src/printer/Manipulators.o \
./src/printer/OutStream.o \
./src/printer/WrapStream.o


# Each subdirectory must supply rules for building sources it contributes
src/printer/%.o: ../src/printer/%.cpp src/printer/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-printer

clean-src-2f-printer:
	-$(RM) ./src/printer/Manipulators.d ./src/printer/Manipulators.o ./src/printer/OutStream.d ./src/printer/OutStream.o ./src/printer/WrapStream.d ./src/printer/WrapStream.o

.PHONY: clean-src-2f-printer

