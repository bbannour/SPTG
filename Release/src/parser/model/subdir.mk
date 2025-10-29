################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/parser/model/ParserUtil.cpp

C_SRCS += \
../src/parser/model/fmlLexer.c \
../src/parser/model/fmlParser.c

OBJS += \
./src/parser/model/ParserUtil.o \
./src/parser/model/fmlLexer.o \
./src/parser/model/fmlParser.o

CPP_DEPS += \
./src/parser/model/ParserUtil.d

C_DEPS += \
./src/parser/model/fmlLexer.d \
./src/parser/model/fmlParser.d


# Each subdirectory must supply rules for building sources it contributes
src/parser/model/%.o: ../src/parser/model/%.cpp src/parser/model/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++-10 -pipe -std=c++17 -D__AVM_LINUX__ -D_GIT_VERSION_=\"$(shell git describe --always --tags)\" -DEXPERIMENTAL_FEATURE -D_ANTLR4_ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_OMEGA_ -D_AVM_SOLVER_CVC4_ -D_AVM_SOLVER_Z3_C_ -D_AVM_SOLVER_YICES_V2_ -U_AVM_BUILTIN_NUMERIC_BOOST_ -I"/home/al203168/_myWorks_/git/intra/org.eclipse.efm-symbex/org.eclipse.efm.symbex/src" -I"/home/al203168/_myWorks_/git/intra/org.eclipse.efm-symbex/org.eclipse.efm.symbex/third-party/include" -I"/home/al203168/_myWorks_/git/intra/org.eclipse.efm-symbex/org.eclipse.efm.symbex/third-party/include/omega" -I/usr/include/antlr4-runtime -O0 -Wall -c -fmessage-length=0 -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '

src/parser/model/%.o: ../src/parser/model/%.c src/parser/model/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C Compiler'
	g++-10 -pipe -std=c11 -D__AVM_LINUX__ -DEXPERIMENTAL_FEATURE -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_OMEGA_ -D_AVM_SOLVER_CVC4_ -D_AVM_SOLVER_Z3_C_ -D_AVM_SOLVER_YICES_V2_ -I"/home/al203168/_myWorks_/git/intra/org.eclipse.efm-symbex/org.eclipse.efm.symbex/src" -I"/home/al203168/_myWorks_/git/intra/org.eclipse.efm-symbex/org.eclipse.efm.symbex/third-party/include" -O0 -w -c -fmessage-length=0  -Wuninitialized -Wunused-function -Wunused-variable -Wunused-but-set-variable -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


