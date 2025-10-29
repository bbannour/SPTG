################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/fml/trace/BasicTraceParser.cpp \
../src/fml/trace/TraceChecker.cpp \
../src/fml/trace/TraceFactory.cpp \
../src/fml/trace/TraceFilter.cpp \
../src/fml/trace/TracePoint.cpp \
../src/fml/trace/TraceSequence.cpp

CPP_DEPS += \
./src/fml/trace/BasicTraceParser.d \
./src/fml/trace/TraceChecker.d \
./src/fml/trace/TraceFactory.d \
./src/fml/trace/TraceFilter.d \
./src/fml/trace/TracePoint.d \
./src/fml/trace/TraceSequence.d

OBJS += \
./src/fml/trace/BasicTraceParser.o \
./src/fml/trace/TraceChecker.o \
./src/fml/trace/TraceFactory.o \
./src/fml/trace/TraceFilter.o \
./src/fml/trace/TracePoint.o \
./src/fml/trace/TraceSequence.o


# Each subdirectory must supply rules for building sources it contributes
src/fml/trace/%.o: ../src/fml/trace/%.cpp src/fml/trace/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-fml-2f-trace

clean-src-2f-fml-2f-trace:
	-$(RM) ./src/fml/trace/BasicTraceParser.d ./src/fml/trace/BasicTraceParser.o ./src/fml/trace/TraceChecker.d ./src/fml/trace/TraceChecker.o ./src/fml/trace/TraceFactory.d ./src/fml/trace/TraceFactory.o ./src/fml/trace/TraceFilter.d ./src/fml/trace/TraceFilter.o ./src/fml/trace/TracePoint.d ./src/fml/trace/TracePoint.o ./src/fml/trace/TraceSequence.d ./src/fml/trace/TraceSequence.o

.PHONY: clean-src-2f-fml-2f-trace

