################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/base/ClassKindInfo.cpp \
../src/base/Injector.cpp \
../src/base/ReferenceCounter.cpp \
../src/base/StaticNullReference.cpp

CPP_DEPS += \
./src/base/ClassKindInfo.d \
./src/base/Injector.d \
./src/base/ReferenceCounter.d \
./src/base/StaticNullReference.d

OBJS += \
./src/base/ClassKindInfo.o \
./src/base/Injector.o \
./src/base/ReferenceCounter.o \
./src/base/StaticNullReference.o


# Each subdirectory must supply rules for building sources it contributes
src/base/%.o: ../src/base/%.cpp src/base/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-base

clean-src-2f-base:
	-$(RM) ./src/base/ClassKindInfo.d ./src/base/ClassKindInfo.o ./src/base/Injector.d ./src/base/Injector.o ./src/base/ReferenceCounter.d ./src/base/ReferenceCounter.o ./src/base/StaticNullReference.d ./src/base/StaticNullReference.o

.PHONY: clean-src-2f-base

