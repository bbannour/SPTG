################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/common/AvmObject.cpp \
../src/common/AvmPointer.cpp \
../src/common/BF.cpp \
../src/common/Element.cpp \
../src/common/NamedElement.cpp \
../src/common/RunnableElement.cpp \
../src/common/SerializerFeature.cpp

CPP_DEPS += \
./src/common/AvmObject.d \
./src/common/AvmPointer.d \
./src/common/BF.d \
./src/common/Element.d \
./src/common/NamedElement.d \
./src/common/RunnableElement.d \
./src/common/SerializerFeature.d

OBJS += \
./src/common/AvmObject.o \
./src/common/AvmPointer.o \
./src/common/BF.o \
./src/common/Element.o \
./src/common/NamedElement.o \
./src/common/RunnableElement.o \
./src/common/SerializerFeature.o


# Each subdirectory must supply rules for building sources it contributes
src/common/%.o: ../src/common/%.cpp src/common/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-common

clean-src-2f-common:
	-$(RM) ./src/common/AvmObject.d ./src/common/AvmObject.o ./src/common/AvmPointer.d ./src/common/AvmPointer.o ./src/common/BF.d ./src/common/BF.o ./src/common/Element.d ./src/common/Element.o ./src/common/NamedElement.d ./src/common/NamedElement.o ./src/common/RunnableElement.d ./src/common/RunnableElement.o ./src/common/SerializerFeature.d ./src/common/SerializerFeature.o

.PHONY: clean-src-2f-common

