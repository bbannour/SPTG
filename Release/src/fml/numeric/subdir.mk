################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/fml/numeric/Float.cpp \
../src/fml/numeric/Integer.cpp \
../src/fml/numeric/Number.cpp \
../src/fml/numeric/Numeric.cpp \
../src/fml/numeric/Rational.cpp

CPP_DEPS += \
./src/fml/numeric/Float.d \
./src/fml/numeric/Integer.d \
./src/fml/numeric/Number.d \
./src/fml/numeric/Numeric.d \
./src/fml/numeric/Rational.d

OBJS += \
./src/fml/numeric/Float.o \
./src/fml/numeric/Integer.o \
./src/fml/numeric/Number.o \
./src/fml/numeric/Numeric.o \
./src/fml/numeric/Rational.o


# Each subdirectory must supply rules for building sources it contributes
src/fml/numeric/%.o: ../src/fml/numeric/%.cpp src/fml/numeric/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-fml-2f-numeric

clean-src-2f-fml-2f-numeric:
	-$(RM) ./src/fml/numeric/Float.d ./src/fml/numeric/Float.o ./src/fml/numeric/Integer.d ./src/fml/numeric/Integer.o ./src/fml/numeric/Number.d ./src/fml/numeric/Number.o ./src/fml/numeric/Numeric.d ./src/fml/numeric/Numeric.o ./src/fml/numeric/Rational.d ./src/fml/numeric/Rational.o

.PHONY: clean-src-2f-fml-2f-numeric

