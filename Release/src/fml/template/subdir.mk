################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/fml/template/TemplateFactory.cpp \
../src/fml/template/TimedMachine.cpp

CPP_DEPS += \
./src/fml/template/TemplateFactory.d \
./src/fml/template/TimedMachine.d

OBJS += \
./src/fml/template/TemplateFactory.o \
./src/fml/template/TimedMachine.o


# Each subdirectory must supply rules for building sources it contributes
src/fml/template/%.o: ../src/fml/template/%.cpp src/fml/template/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-fml-2f-template

clean-src-2f-fml-2f-template:
	-$(RM) ./src/fml/template/TemplateFactory.d ./src/fml/template/TemplateFactory.o ./src/fml/template/TimedMachine.d ./src/fml/template/TimedMachine.o

.PHONY: clean-src-2f-fml-2f-template

