################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/famcore/trace/AbstractTraceBuilder.cpp \
../src/famcore/trace/AbstractTraceFormatter.cpp \
../src/famcore/trace/AvmTraceGenerator.cpp \
../src/famcore/trace/BasicTraceBuilder.cpp \
../src/famcore/trace/BasicTraceFormatter.cpp \
../src/famcore/trace/SequenceDiagramTraceBuilder.cpp \
../src/famcore/trace/SequenceDiagramTraceFormatter.cpp \
../src/famcore/trace/TTCNBaseTraceFormatter.cpp \
../src/famcore/trace/TTCNTitanTraceFormatter.cpp \
../src/famcore/trace/TTCNTraceFormatter.cpp \
../src/famcore/trace/TraceManager.cpp \
../src/famcore/trace/TraceNormalizer.cpp \
../src/famcore/trace/TraceNumerizer.cpp

CPP_DEPS += \
./src/famcore/trace/AbstractTraceBuilder.d \
./src/famcore/trace/AbstractTraceFormatter.d \
./src/famcore/trace/AvmTraceGenerator.d \
./src/famcore/trace/BasicTraceBuilder.d \
./src/famcore/trace/BasicTraceFormatter.d \
./src/famcore/trace/SequenceDiagramTraceBuilder.d \
./src/famcore/trace/SequenceDiagramTraceFormatter.d \
./src/famcore/trace/TTCNBaseTraceFormatter.d \
./src/famcore/trace/TTCNTitanTraceFormatter.d \
./src/famcore/trace/TTCNTraceFormatter.d \
./src/famcore/trace/TraceManager.d \
./src/famcore/trace/TraceNormalizer.d \
./src/famcore/trace/TraceNumerizer.d

OBJS += \
./src/famcore/trace/AbstractTraceBuilder.o \
./src/famcore/trace/AbstractTraceFormatter.o \
./src/famcore/trace/AvmTraceGenerator.o \
./src/famcore/trace/BasicTraceBuilder.o \
./src/famcore/trace/BasicTraceFormatter.o \
./src/famcore/trace/SequenceDiagramTraceBuilder.o \
./src/famcore/trace/SequenceDiagramTraceFormatter.o \
./src/famcore/trace/TTCNBaseTraceFormatter.o \
./src/famcore/trace/TTCNTitanTraceFormatter.o \
./src/famcore/trace/TTCNTraceFormatter.o \
./src/famcore/trace/TraceManager.o \
./src/famcore/trace/TraceNormalizer.o \
./src/famcore/trace/TraceNumerizer.o


# Each subdirectory must supply rules for building sources it contributes
src/famcore/trace/%.o: ../src/famcore/trace/%.cpp src/famcore/trace/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-famcore-2f-trace

clean-src-2f-famcore-2f-trace:
	-$(RM) ./src/famcore/trace/AbstractTraceBuilder.d ./src/famcore/trace/AbstractTraceBuilder.o ./src/famcore/trace/AbstractTraceFormatter.d ./src/famcore/trace/AbstractTraceFormatter.o ./src/famcore/trace/AvmTraceGenerator.d ./src/famcore/trace/AvmTraceGenerator.o ./src/famcore/trace/BasicTraceBuilder.d ./src/famcore/trace/BasicTraceBuilder.o ./src/famcore/trace/BasicTraceFormatter.d ./src/famcore/trace/BasicTraceFormatter.o ./src/famcore/trace/SequenceDiagramTraceBuilder.d ./src/famcore/trace/SequenceDiagramTraceBuilder.o ./src/famcore/trace/SequenceDiagramTraceFormatter.d ./src/famcore/trace/SequenceDiagramTraceFormatter.o ./src/famcore/trace/TTCNBaseTraceFormatter.d ./src/famcore/trace/TTCNBaseTraceFormatter.o ./src/famcore/trace/TTCNTitanTraceFormatter.d ./src/famcore/trace/TTCNTitanTraceFormatter.o ./src/famcore/trace/TTCNTraceFormatter.d ./src/famcore/trace/TTCNTraceFormatter.o ./src/famcore/trace/TraceManager.d ./src/famcore/trace/TraceManager.o ./src/famcore/trace/TraceNormalizer.d ./src/famcore/trace/TraceNormalizer.o ./src/famcore/trace/TraceNumerizer.d ./src/famcore/trace/TraceNumerizer.o

.PHONY: clean-src-2f-famcore-2f-trace

