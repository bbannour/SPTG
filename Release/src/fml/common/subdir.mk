################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/fml/common/BasePointer.cpp \
../src/fml/common/BehavioralElement.cpp \
../src/fml/common/CompiledElement.cpp \
../src/fml/common/LifecycleElement.cpp \
../src/fml/common/LocationElement.cpp \
../src/fml/common/ModifierElement.cpp \
../src/fml/common/ObjectClassifier.cpp \
../src/fml/common/ObjectElement.cpp \
../src/fml/common/PropertyElement.cpp \
../src/fml/common/SpecifierElement.cpp \
../src/fml/common/TraceableElement.cpp

CPP_DEPS += \
./src/fml/common/BasePointer.d \
./src/fml/common/BehavioralElement.d \
./src/fml/common/CompiledElement.d \
./src/fml/common/LifecycleElement.d \
./src/fml/common/LocationElement.d \
./src/fml/common/ModifierElement.d \
./src/fml/common/ObjectClassifier.d \
./src/fml/common/ObjectElement.d \
./src/fml/common/PropertyElement.d \
./src/fml/common/SpecifierElement.d \
./src/fml/common/TraceableElement.d

OBJS += \
./src/fml/common/BasePointer.o \
./src/fml/common/BehavioralElement.o \
./src/fml/common/CompiledElement.o \
./src/fml/common/LifecycleElement.o \
./src/fml/common/LocationElement.o \
./src/fml/common/ModifierElement.o \
./src/fml/common/ObjectClassifier.o \
./src/fml/common/ObjectElement.o \
./src/fml/common/PropertyElement.o \
./src/fml/common/SpecifierElement.o \
./src/fml/common/TraceableElement.o


# Each subdirectory must supply rules for building sources it contributes
src/fml/common/%.o: ../src/fml/common/%.cpp src/fml/common/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-fml-2f-common

clean-src-2f-fml-2f-common:
	-$(RM) ./src/fml/common/BasePointer.d ./src/fml/common/BasePointer.o ./src/fml/common/BehavioralElement.d ./src/fml/common/BehavioralElement.o ./src/fml/common/CompiledElement.d ./src/fml/common/CompiledElement.o ./src/fml/common/LifecycleElement.d ./src/fml/common/LifecycleElement.o ./src/fml/common/LocationElement.d ./src/fml/common/LocationElement.o ./src/fml/common/ModifierElement.d ./src/fml/common/ModifierElement.o ./src/fml/common/ObjectClassifier.d ./src/fml/common/ObjectClassifier.o ./src/fml/common/ObjectElement.d ./src/fml/common/ObjectElement.o ./src/fml/common/PropertyElement.d ./src/fml/common/PropertyElement.o ./src/fml/common/SpecifierElement.d ./src/fml/common/SpecifierElement.o ./src/fml/common/TraceableElement.d ./src/fml/common/TraceableElement.o

.PHONY: clean-src-2f-fml-2f-common

