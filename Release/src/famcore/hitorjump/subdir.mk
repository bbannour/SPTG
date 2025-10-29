################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/famcore/hitorjump/AvmHitOrJumpProcessor.cpp \
../src/famcore/hitorjump/BaseHitProcessor.cpp \
../src/famcore/hitorjump/HitOrderedProcessor.cpp \
../src/famcore/hitorjump/HitUnorderedProcessor.cpp

CPP_DEPS += \
./src/famcore/hitorjump/AvmHitOrJumpProcessor.d \
./src/famcore/hitorjump/BaseHitProcessor.d \
./src/famcore/hitorjump/HitOrderedProcessor.d \
./src/famcore/hitorjump/HitUnorderedProcessor.d

OBJS += \
./src/famcore/hitorjump/AvmHitOrJumpProcessor.o \
./src/famcore/hitorjump/BaseHitProcessor.o \
./src/famcore/hitorjump/HitOrderedProcessor.o \
./src/famcore/hitorjump/HitUnorderedProcessor.o


# Each subdirectory must supply rules for building sources it contributes
src/famcore/hitorjump/%.o: ../src/famcore/hitorjump/%.cpp src/famcore/hitorjump/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-famcore-2f-hitorjump

clean-src-2f-famcore-2f-hitorjump:
	-$(RM) ./src/famcore/hitorjump/AvmHitOrJumpProcessor.d ./src/famcore/hitorjump/AvmHitOrJumpProcessor.o ./src/famcore/hitorjump/BaseHitProcessor.d ./src/famcore/hitorjump/BaseHitProcessor.o ./src/famcore/hitorjump/HitOrderedProcessor.d ./src/famcore/hitorjump/HitOrderedProcessor.o ./src/famcore/hitorjump/HitUnorderedProcessor.d ./src/famcore/hitorjump/HitUnorderedProcessor.o

.PHONY: clean-src-2f-famcore-2f-hitorjump

