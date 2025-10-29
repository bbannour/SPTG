################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/famcore/api/AbstractProcessorUnit.cpp \
../src/famcore/api/AvmCoverageHeuristicProperty.cpp \
../src/famcore/api/BaseCoverageFilter.cpp \
../src/famcore/api/CompositeControllerUnit.cpp \
../src/famcore/api/ExtenderProcessorUnit.cpp \
../src/famcore/api/IProcessorUnitTest.cpp \
../src/famcore/api/MainProcessorUnit.cpp \
../src/famcore/api/ProcessorUnitAutoRegistration.cpp \
../src/famcore/api/ProcessorUnitFactory.cpp \
../src/famcore/api/ProcessorUnitRepository.cpp

CPP_DEPS += \
./src/famcore/api/AbstractProcessorUnit.d \
./src/famcore/api/AvmCoverageHeuristicProperty.d \
./src/famcore/api/BaseCoverageFilter.d \
./src/famcore/api/CompositeControllerUnit.d \
./src/famcore/api/ExtenderProcessorUnit.d \
./src/famcore/api/IProcessorUnitTest.d \
./src/famcore/api/MainProcessorUnit.d \
./src/famcore/api/ProcessorUnitAutoRegistration.d \
./src/famcore/api/ProcessorUnitFactory.d \
./src/famcore/api/ProcessorUnitRepository.d

OBJS += \
./src/famcore/api/AbstractProcessorUnit.o \
./src/famcore/api/AvmCoverageHeuristicProperty.o \
./src/famcore/api/BaseCoverageFilter.o \
./src/famcore/api/CompositeControllerUnit.o \
./src/famcore/api/ExtenderProcessorUnit.o \
./src/famcore/api/IProcessorUnitTest.o \
./src/famcore/api/MainProcessorUnit.o \
./src/famcore/api/ProcessorUnitAutoRegistration.o \
./src/famcore/api/ProcessorUnitFactory.o \
./src/famcore/api/ProcessorUnitRepository.o


# Each subdirectory must supply rules for building sources it contributes
src/famcore/api/%.o: ../src/famcore/api/%.cpp src/famcore/api/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-famcore-2f-api

clean-src-2f-famcore-2f-api:
	-$(RM) ./src/famcore/api/AbstractProcessorUnit.d ./src/famcore/api/AbstractProcessorUnit.o ./src/famcore/api/AvmCoverageHeuristicProperty.d ./src/famcore/api/AvmCoverageHeuristicProperty.o ./src/famcore/api/BaseCoverageFilter.d ./src/famcore/api/BaseCoverageFilter.o ./src/famcore/api/CompositeControllerUnit.d ./src/famcore/api/CompositeControllerUnit.o ./src/famcore/api/ExtenderProcessorUnit.d ./src/famcore/api/ExtenderProcessorUnit.o ./src/famcore/api/IProcessorUnitTest.d ./src/famcore/api/IProcessorUnitTest.o ./src/famcore/api/MainProcessorUnit.d ./src/famcore/api/MainProcessorUnit.o ./src/famcore/api/ProcessorUnitAutoRegistration.d ./src/famcore/api/ProcessorUnitAutoRegistration.o ./src/famcore/api/ProcessorUnitFactory.d ./src/famcore/api/ProcessorUnitFactory.o ./src/famcore/api/ProcessorUnitRepository.d ./src/famcore/api/ProcessorUnitRepository.o

.PHONY: clean-src-2f-famcore-2f-api

