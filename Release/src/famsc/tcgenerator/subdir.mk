################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/famsc/tcgenerator/AvmDeadBranchPruner.cpp \
../src/famsc/tcgenerator/AvmOutputNormalizer.cpp \
../src/famsc/tcgenerator/AvmPathGuidedTestcaseGenerator.cpp \
../src/famsc/tcgenerator/AvmQuiescenceFactory.cpp \
../src/famsc/tcgenerator/AvmTestCaseFactory.cpp \
../src/famsc/tcgenerator/AvmTestCaseFactorySimplified.cpp \
../src/famsc/tcgenerator/AvmTestCaseStatistics.cpp \
../src/famsc/tcgenerator/AvmTestCaseUtils.cpp \
../src/famsc/tcgenerator/AvmTraceDeterminismFactory.cpp

CPP_DEPS += \
./src/famsc/tcgenerator/AvmDeadBranchPruner.d \
./src/famsc/tcgenerator/AvmOutputNormalizer.d \
./src/famsc/tcgenerator/AvmPathGuidedTestcaseGenerator.d \
./src/famsc/tcgenerator/AvmQuiescenceFactory.d \
./src/famsc/tcgenerator/AvmTestCaseFactory.d \
./src/famsc/tcgenerator/AvmTestCaseFactorySimplified.d \
./src/famsc/tcgenerator/AvmTestCaseStatistics.d \
./src/famsc/tcgenerator/AvmTestCaseUtils.d \
./src/famsc/tcgenerator/AvmTraceDeterminismFactory.d

OBJS += \
./src/famsc/tcgenerator/AvmDeadBranchPruner.o \
./src/famsc/tcgenerator/AvmOutputNormalizer.o \
./src/famsc/tcgenerator/AvmPathGuidedTestcaseGenerator.o \
./src/famsc/tcgenerator/AvmQuiescenceFactory.o \
./src/famsc/tcgenerator/AvmTestCaseFactory.o \
./src/famsc/tcgenerator/AvmTestCaseFactorySimplified.o \
./src/famsc/tcgenerator/AvmTestCaseStatistics.o \
./src/famsc/tcgenerator/AvmTestCaseUtils.o \
./src/famsc/tcgenerator/AvmTraceDeterminismFactory.o


# Each subdirectory must supply rules for building sources it contributes
src/famsc/tcgenerator/%.o: ../src/famsc/tcgenerator/%.cpp src/famsc/tcgenerator/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-famsc-2f-tcgenerator

clean-src-2f-famsc-2f-tcgenerator:
	-$(RM) ./src/famsc/tcgenerator/AvmDeadBranchPruner.d ./src/famsc/tcgenerator/AvmDeadBranchPruner.o ./src/famsc/tcgenerator/AvmOutputNormalizer.d ./src/famsc/tcgenerator/AvmOutputNormalizer.o ./src/famsc/tcgenerator/AvmPathGuidedTestcaseGenerator.d ./src/famsc/tcgenerator/AvmPathGuidedTestcaseGenerator.o ./src/famsc/tcgenerator/AvmQuiescenceFactory.d ./src/famsc/tcgenerator/AvmQuiescenceFactory.o ./src/famsc/tcgenerator/AvmTestCaseFactory.d ./src/famsc/tcgenerator/AvmTestCaseFactory.o ./src/famsc/tcgenerator/AvmTestCaseFactorySimplified.d ./src/famsc/tcgenerator/AvmTestCaseFactorySimplified.o ./src/famsc/tcgenerator/AvmTestCaseStatistics.d ./src/famsc/tcgenerator/AvmTestCaseStatistics.o ./src/famsc/tcgenerator/AvmTestCaseUtils.d ./src/famsc/tcgenerator/AvmTestCaseUtils.o ./src/famsc/tcgenerator/AvmTraceDeterminismFactory.d ./src/famsc/tcgenerator/AvmTraceDeterminismFactory.o

.PHONY: clean-src-2f-famsc-2f-tcgenerator

