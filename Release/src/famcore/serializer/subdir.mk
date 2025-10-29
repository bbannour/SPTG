################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/famcore/serializer/AvmCode2Puml.cpp \
../src/famcore/serializer/CommonExecutionGraphSerializer.cpp \
../src/famcore/serializer/CommonGraphicStatemachineSerializer.cpp \
../src/famcore/serializer/CommunicationGraphSerializer.cpp \
../src/famcore/serializer/GraphVizExecutionGraphSerializer.cpp \
../src/famcore/serializer/GraphVizStatemachineSerializer.cpp \
../src/famcore/serializer/GraphicExecutionGraphSerializer.cpp \
../src/famcore/serializer/GraphicStatemachineSerializer.cpp \
../src/famcore/serializer/Serializer.cpp

CPP_DEPS += \
./src/famcore/serializer/AvmCode2Puml.d \
./src/famcore/serializer/CommonExecutionGraphSerializer.d \
./src/famcore/serializer/CommonGraphicStatemachineSerializer.d \
./src/famcore/serializer/CommunicationGraphSerializer.d \
./src/famcore/serializer/GraphVizExecutionGraphSerializer.d \
./src/famcore/serializer/GraphVizStatemachineSerializer.d \
./src/famcore/serializer/GraphicExecutionGraphSerializer.d \
./src/famcore/serializer/GraphicStatemachineSerializer.d \
./src/famcore/serializer/Serializer.d

OBJS += \
./src/famcore/serializer/AvmCode2Puml.o \
./src/famcore/serializer/CommonExecutionGraphSerializer.o \
./src/famcore/serializer/CommonGraphicStatemachineSerializer.o \
./src/famcore/serializer/CommunicationGraphSerializer.o \
./src/famcore/serializer/GraphVizExecutionGraphSerializer.o \
./src/famcore/serializer/GraphVizStatemachineSerializer.o \
./src/famcore/serializer/GraphicExecutionGraphSerializer.o \
./src/famcore/serializer/GraphicStatemachineSerializer.o \
./src/famcore/serializer/Serializer.o


# Each subdirectory must supply rules for building sources it contributes
src/famcore/serializer/%.o: ../src/famcore/serializer/%.cpp src/famcore/serializer/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-famcore-2f-serializer

clean-src-2f-famcore-2f-serializer:
	-$(RM) ./src/famcore/serializer/AvmCode2Puml.d ./src/famcore/serializer/AvmCode2Puml.o ./src/famcore/serializer/CommonExecutionGraphSerializer.d ./src/famcore/serializer/CommonExecutionGraphSerializer.o ./src/famcore/serializer/CommonGraphicStatemachineSerializer.d ./src/famcore/serializer/CommonGraphicStatemachineSerializer.o ./src/famcore/serializer/CommunicationGraphSerializer.d ./src/famcore/serializer/CommunicationGraphSerializer.o ./src/famcore/serializer/GraphVizExecutionGraphSerializer.d ./src/famcore/serializer/GraphVizExecutionGraphSerializer.o ./src/famcore/serializer/GraphVizStatemachineSerializer.d ./src/famcore/serializer/GraphVizStatemachineSerializer.o ./src/famcore/serializer/GraphicExecutionGraphSerializer.d ./src/famcore/serializer/GraphicExecutionGraphSerializer.o ./src/famcore/serializer/GraphicStatemachineSerializer.d ./src/famcore/serializer/GraphicStatemachineSerializer.o ./src/famcore/serializer/Serializer.d ./src/famcore/serializer/Serializer.o

.PHONY: clean-src-2f-famcore-2f-serializer

