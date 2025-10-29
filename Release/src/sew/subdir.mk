################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/sew/Configuration.cpp \
../src/sew/SymbexController.cpp \
../src/sew/SymbexControllerEventManager.cpp \
../src/sew/SymbexControllerRequestManager.cpp \
../src/sew/SymbexControllerUnitManager.cpp \
../src/sew/SymbexDispatcher.cpp \
../src/sew/SymbexEngine.cpp \
../src/sew/SymbexProcessor.cpp \
../src/sew/Workflow.cpp \
../src/sew/WorkflowParameter.cpp

CPP_DEPS += \
./src/sew/Configuration.d \
./src/sew/SymbexController.d \
./src/sew/SymbexControllerEventManager.d \
./src/sew/SymbexControllerRequestManager.d \
./src/sew/SymbexControllerUnitManager.d \
./src/sew/SymbexDispatcher.d \
./src/sew/SymbexEngine.d \
./src/sew/SymbexProcessor.d \
./src/sew/Workflow.d \
./src/sew/WorkflowParameter.d

OBJS += \
./src/sew/Configuration.o \
./src/sew/SymbexController.o \
./src/sew/SymbexControllerEventManager.o \
./src/sew/SymbexControllerRequestManager.o \
./src/sew/SymbexControllerUnitManager.o \
./src/sew/SymbexDispatcher.o \
./src/sew/SymbexEngine.o \
./src/sew/SymbexProcessor.o \
./src/sew/Workflow.o \
./src/sew/WorkflowParameter.o


# Each subdirectory must supply rules for building sources it contributes
src/sew/%.o: ../src/sew/%.cpp src/sew/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-sew

clean-src-2f-sew:
	-$(RM) ./src/sew/Configuration.d ./src/sew/Configuration.o ./src/sew/SymbexController.d ./src/sew/SymbexController.o ./src/sew/SymbexControllerEventManager.d ./src/sew/SymbexControllerEventManager.o ./src/sew/SymbexControllerRequestManager.d ./src/sew/SymbexControllerRequestManager.o ./src/sew/SymbexControllerUnitManager.d ./src/sew/SymbexControllerUnitManager.o ./src/sew/SymbexDispatcher.d ./src/sew/SymbexDispatcher.o ./src/sew/SymbexEngine.d ./src/sew/SymbexEngine.o ./src/sew/SymbexProcessor.d ./src/sew/SymbexProcessor.o ./src/sew/Workflow.d ./src/sew/Workflow.o ./src/sew/WorkflowParameter.d ./src/sew/WorkflowParameter.o

.PHONY: clean-src-2f-sew

