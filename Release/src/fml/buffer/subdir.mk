################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/fml/buffer/BaseBufferForm.cpp \
../src/fml/buffer/BaseBufferQueue.cpp \
../src/fml/buffer/BroadcastBuffer.cpp \
../src/fml/buffer/FifoBuffer.cpp \
../src/fml/buffer/LifoBuffer.cpp \
../src/fml/buffer/MultiFifoBuffer.cpp \
../src/fml/buffer/MultiLifoBuffer.cpp \
../src/fml/buffer/RamBuffer.cpp \
../src/fml/buffer/SetBuffer.cpp

CPP_DEPS += \
./src/fml/buffer/BaseBufferForm.d \
./src/fml/buffer/BaseBufferQueue.d \
./src/fml/buffer/BroadcastBuffer.d \
./src/fml/buffer/FifoBuffer.d \
./src/fml/buffer/LifoBuffer.d \
./src/fml/buffer/MultiFifoBuffer.d \
./src/fml/buffer/MultiLifoBuffer.d \
./src/fml/buffer/RamBuffer.d \
./src/fml/buffer/SetBuffer.d

OBJS += \
./src/fml/buffer/BaseBufferForm.o \
./src/fml/buffer/BaseBufferQueue.o \
./src/fml/buffer/BroadcastBuffer.o \
./src/fml/buffer/FifoBuffer.o \
./src/fml/buffer/LifoBuffer.o \
./src/fml/buffer/MultiFifoBuffer.o \
./src/fml/buffer/MultiLifoBuffer.o \
./src/fml/buffer/RamBuffer.o \
./src/fml/buffer/SetBuffer.o


# Each subdirectory must supply rules for building sources it contributes
src/fml/buffer/%.o: ../src/fml/buffer/%.cpp src/fml/buffer/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-fml-2f-buffer

clean-src-2f-fml-2f-buffer:
	-$(RM) ./src/fml/buffer/BaseBufferForm.d ./src/fml/buffer/BaseBufferForm.o ./src/fml/buffer/BaseBufferQueue.d ./src/fml/buffer/BaseBufferQueue.o ./src/fml/buffer/BroadcastBuffer.d ./src/fml/buffer/BroadcastBuffer.o ./src/fml/buffer/FifoBuffer.d ./src/fml/buffer/FifoBuffer.o ./src/fml/buffer/LifoBuffer.d ./src/fml/buffer/LifoBuffer.o ./src/fml/buffer/MultiFifoBuffer.d ./src/fml/buffer/MultiFifoBuffer.o ./src/fml/buffer/MultiLifoBuffer.d ./src/fml/buffer/MultiLifoBuffer.o ./src/fml/buffer/RamBuffer.d ./src/fml/buffer/RamBuffer.o ./src/fml/buffer/SetBuffer.d ./src/fml/buffer/SetBuffer.o

.PHONY: clean-src-2f-fml-2f-buffer

