################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/famsc/testing/OfflineTestHelper.cpp \
../src/famsc/testing/OfflineTestProcessor.cpp

CPP_DEPS += \
./src/famsc/testing/OfflineTestHelper.d \
./src/famsc/testing/OfflineTestProcessor.d

OBJS += \
./src/famsc/testing/OfflineTestHelper.o \
./src/famsc/testing/OfflineTestProcessor.o


# Each subdirectory must supply rules for building sources it contributes
src/famsc/testing/%.o: ../src/famsc/testing/%.cpp src/famsc/testing/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-famsc-2f-testing

clean-src-2f-famsc-2f-testing:
	-$(RM) ./src/famsc/testing/OfflineTestHelper.d ./src/famsc/testing/OfflineTestHelper.o ./src/famsc/testing/OfflineTestProcessor.d ./src/famsc/testing/OfflineTestProcessor.o

.PHONY: clean-src-2f-famsc-2f-testing

