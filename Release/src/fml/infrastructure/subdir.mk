################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/fml/infrastructure/BehavioralPart.cpp \
../src/fml/infrastructure/Buffer.cpp \
../src/fml/infrastructure/Channel.cpp \
../src/fml/infrastructure/ComPoint.cpp \
../src/fml/infrastructure/ComProtocol.cpp \
../src/fml/infrastructure/ComRoute.cpp \
../src/fml/infrastructure/CompositePart.cpp \
../src/fml/infrastructure/Connector.cpp \
../src/fml/infrastructure/DataType.cpp \
../src/fml/infrastructure/Function.cpp \
../src/fml/infrastructure/InstanceSpecifierPart.cpp \
../src/fml/infrastructure/InteractionPart.cpp \
../src/fml/infrastructure/Machine.cpp \
../src/fml/infrastructure/MachineQuery.cpp \
../src/fml/infrastructure/ModelOfComputationPart.cpp \
../src/fml/infrastructure/Package.cpp \
../src/fml/infrastructure/Port.cpp \
../src/fml/infrastructure/PropertyPart.cpp \
../src/fml/infrastructure/Routine.cpp \
../src/fml/infrastructure/System.cpp \
../src/fml/infrastructure/Transition.cpp \
../src/fml/infrastructure/TransitionMoc.cpp \
../src/fml/infrastructure/Variable.cpp

CPP_DEPS += \
./src/fml/infrastructure/BehavioralPart.d \
./src/fml/infrastructure/Buffer.d \
./src/fml/infrastructure/Channel.d \
./src/fml/infrastructure/ComPoint.d \
./src/fml/infrastructure/ComProtocol.d \
./src/fml/infrastructure/ComRoute.d \
./src/fml/infrastructure/CompositePart.d \
./src/fml/infrastructure/Connector.d \
./src/fml/infrastructure/DataType.d \
./src/fml/infrastructure/Function.d \
./src/fml/infrastructure/InstanceSpecifierPart.d \
./src/fml/infrastructure/InteractionPart.d \
./src/fml/infrastructure/Machine.d \
./src/fml/infrastructure/MachineQuery.d \
./src/fml/infrastructure/ModelOfComputationPart.d \
./src/fml/infrastructure/Package.d \
./src/fml/infrastructure/Port.d \
./src/fml/infrastructure/PropertyPart.d \
./src/fml/infrastructure/Routine.d \
./src/fml/infrastructure/System.d \
./src/fml/infrastructure/Transition.d \
./src/fml/infrastructure/TransitionMoc.d \
./src/fml/infrastructure/Variable.d

OBJS += \
./src/fml/infrastructure/BehavioralPart.o \
./src/fml/infrastructure/Buffer.o \
./src/fml/infrastructure/Channel.o \
./src/fml/infrastructure/ComPoint.o \
./src/fml/infrastructure/ComProtocol.o \
./src/fml/infrastructure/ComRoute.o \
./src/fml/infrastructure/CompositePart.o \
./src/fml/infrastructure/Connector.o \
./src/fml/infrastructure/DataType.o \
./src/fml/infrastructure/Function.o \
./src/fml/infrastructure/InstanceSpecifierPart.o \
./src/fml/infrastructure/InteractionPart.o \
./src/fml/infrastructure/Machine.o \
./src/fml/infrastructure/MachineQuery.o \
./src/fml/infrastructure/ModelOfComputationPart.o \
./src/fml/infrastructure/Package.o \
./src/fml/infrastructure/Port.o \
./src/fml/infrastructure/PropertyPart.o \
./src/fml/infrastructure/Routine.o \
./src/fml/infrastructure/System.o \
./src/fml/infrastructure/Transition.o \
./src/fml/infrastructure/TransitionMoc.o \
./src/fml/infrastructure/Variable.o


# Each subdirectory must supply rules for building sources it contributes
src/fml/infrastructure/%.o: ../src/fml/infrastructure/%.cpp src/fml/infrastructure/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-fml-2f-infrastructure

clean-src-2f-fml-2f-infrastructure:
	-$(RM) ./src/fml/infrastructure/BehavioralPart.d ./src/fml/infrastructure/BehavioralPart.o ./src/fml/infrastructure/Buffer.d ./src/fml/infrastructure/Buffer.o ./src/fml/infrastructure/Channel.d ./src/fml/infrastructure/Channel.o ./src/fml/infrastructure/ComPoint.d ./src/fml/infrastructure/ComPoint.o ./src/fml/infrastructure/ComProtocol.d ./src/fml/infrastructure/ComProtocol.o ./src/fml/infrastructure/ComRoute.d ./src/fml/infrastructure/ComRoute.o ./src/fml/infrastructure/CompositePart.d ./src/fml/infrastructure/CompositePart.o ./src/fml/infrastructure/Connector.d ./src/fml/infrastructure/Connector.o ./src/fml/infrastructure/DataType.d ./src/fml/infrastructure/DataType.o ./src/fml/infrastructure/Function.d ./src/fml/infrastructure/Function.o ./src/fml/infrastructure/InstanceSpecifierPart.d ./src/fml/infrastructure/InstanceSpecifierPart.o ./src/fml/infrastructure/InteractionPart.d ./src/fml/infrastructure/InteractionPart.o ./src/fml/infrastructure/Machine.d ./src/fml/infrastructure/Machine.o ./src/fml/infrastructure/MachineQuery.d ./src/fml/infrastructure/MachineQuery.o ./src/fml/infrastructure/ModelOfComputationPart.d ./src/fml/infrastructure/ModelOfComputationPart.o ./src/fml/infrastructure/Package.d ./src/fml/infrastructure/Package.o ./src/fml/infrastructure/Port.d ./src/fml/infrastructure/Port.o ./src/fml/infrastructure/PropertyPart.d ./src/fml/infrastructure/PropertyPart.o ./src/fml/infrastructure/Routine.d ./src/fml/infrastructure/Routine.o ./src/fml/infrastructure/System.d ./src/fml/infrastructure/System.o ./src/fml/infrastructure/Transition.d ./src/fml/infrastructure/Transition.o ./src/fml/infrastructure/TransitionMoc.d ./src/fml/infrastructure/TransitionMoc.o ./src/fml/infrastructure/Variable.d ./src/fml/infrastructure/Variable.o

.PHONY: clean-src-2f-fml-2f-infrastructure

