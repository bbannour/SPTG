################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/fml/builtin/Boolean.cpp \
../src/fml/builtin/BuiltinForm.cpp \
../src/fml/builtin/Character.cpp \
../src/fml/builtin/Identifier.cpp \
../src/fml/builtin/QualifiedIdentifier.cpp \
../src/fml/builtin/String.cpp

CPP_DEPS += \
./src/fml/builtin/Boolean.d \
./src/fml/builtin/BuiltinForm.d \
./src/fml/builtin/Character.d \
./src/fml/builtin/Identifier.d \
./src/fml/builtin/QualifiedIdentifier.d \
./src/fml/builtin/String.d

OBJS += \
./src/fml/builtin/Boolean.o \
./src/fml/builtin/BuiltinForm.o \
./src/fml/builtin/Character.o \
./src/fml/builtin/Identifier.o \
./src/fml/builtin/QualifiedIdentifier.o \
./src/fml/builtin/String.o


# Each subdirectory must supply rules for building sources it contributes
src/fml/builtin/%.o: ../src/fml/builtin/%.cpp src/fml/builtin/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-fml-2f-builtin

clean-src-2f-fml-2f-builtin:
	-$(RM) ./src/fml/builtin/Boolean.d ./src/fml/builtin/Boolean.o ./src/fml/builtin/BuiltinForm.d ./src/fml/builtin/BuiltinForm.o ./src/fml/builtin/Character.d ./src/fml/builtin/Character.o ./src/fml/builtin/Identifier.d ./src/fml/builtin/Identifier.o ./src/fml/builtin/QualifiedIdentifier.d ./src/fml/builtin/QualifiedIdentifier.o ./src/fml/builtin/String.d ./src/fml/builtin/String.o

.PHONY: clean-src-2f-fml-2f-builtin

