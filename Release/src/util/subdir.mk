################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/util/BoostFactory.cpp \
../src/util/ExecutionChrono.cpp \
../src/util/ExecutionTime.cpp \
../src/util/avm_assert.cpp \
../src/util/avm_debug.cpp \
../src/util/avm_numeric.cpp \
../src/util/avm_string.cpp \
../src/util/avm_types.cpp \
../src/util/avm_uri.cpp \
../src/util/avm_util.cpp \
../src/util/avm_vfs.cpp

CPP_DEPS += \
./src/util/BoostFactory.d \
./src/util/ExecutionChrono.d \
./src/util/ExecutionTime.d \
./src/util/avm_assert.d \
./src/util/avm_debug.d \
./src/util/avm_numeric.d \
./src/util/avm_string.d \
./src/util/avm_types.d \
./src/util/avm_uri.d \
./src/util/avm_util.d \
./src/util/avm_vfs.d

OBJS += \
./src/util/BoostFactory.o \
./src/util/ExecutionChrono.o \
./src/util/ExecutionTime.o \
./src/util/avm_assert.o \
./src/util/avm_debug.o \
./src/util/avm_numeric.o \
./src/util/avm_string.o \
./src/util/avm_types.o \
./src/util/avm_uri.o \
./src/util/avm_util.o \
./src/util/avm_vfs.o


# Each subdirectory must supply rules for building sources it contributes
src/util/%.o: ../src/util/%.cpp src/util/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-util

clean-src-2f-util:
	-$(RM) ./src/util/BoostFactory.d ./src/util/BoostFactory.o ./src/util/ExecutionChrono.d ./src/util/ExecutionChrono.o ./src/util/ExecutionTime.d ./src/util/ExecutionTime.o ./src/util/avm_assert.d ./src/util/avm_assert.o ./src/util/avm_debug.d ./src/util/avm_debug.o ./src/util/avm_numeric.d ./src/util/avm_numeric.o ./src/util/avm_string.d ./src/util/avm_string.o ./src/util/avm_types.d ./src/util/avm_types.o ./src/util/avm_uri.d ./src/util/avm_uri.o ./src/util/avm_util.d ./src/util/avm_util.o ./src/util/avm_vfs.d ./src/util/avm_vfs.o

.PHONY: clean-src-2f-util

