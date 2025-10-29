################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/fml/workflow/Query.cpp \
../src/fml/workflow/UniFormIdentifier.cpp \
../src/fml/workflow/WObject.cpp \
../src/fml/workflow/WPropertyImpl.cpp

CPP_DEPS += \
./src/fml/workflow/Query.d \
./src/fml/workflow/UniFormIdentifier.d \
./src/fml/workflow/WObject.d \
./src/fml/workflow/WPropertyImpl.d

OBJS += \
./src/fml/workflow/Query.o \
./src/fml/workflow/UniFormIdentifier.o \
./src/fml/workflow/WObject.o \
./src/fml/workflow/WPropertyImpl.o


# Each subdirectory must supply rules for building sources it contributes
src/fml/workflow/%.o: ../src/fml/workflow/%.cpp src/fml/workflow/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-fml-2f-workflow

clean-src-2f-fml-2f-workflow:
	-$(RM) ./src/fml/workflow/Query.d ./src/fml/workflow/Query.o ./src/fml/workflow/UniFormIdentifier.d ./src/fml/workflow/UniFormIdentifier.o ./src/fml/workflow/WObject.d ./src/fml/workflow/WObject.o ./src/fml/workflow/WPropertyImpl.d ./src/fml/workflow/WPropertyImpl.o

.PHONY: clean-src-2f-fml-2f-workflow

