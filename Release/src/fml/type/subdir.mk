################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables
CPP_SRCS += \
../src/fml/type/BaseSymbolTypeSpecifier.cpp \
../src/fml/type/BaseTypeSpecifier.cpp \
../src/fml/type/ChoiceTypeSpecifier.cpp \
../src/fml/type/ClassTypeSpecifier.cpp \
../src/fml/type/ContainerTypeSpecifier.cpp \
../src/fml/type/EnumTypeSpecifier.cpp \
../src/fml/type/IntervalTypeSpecifier.cpp \
../src/fml/type/TableOfTypeSpecifier.cpp \
../src/fml/type/TypeAliasSpecifier.cpp \
../src/fml/type/TypeManager.cpp \
../src/fml/type/TypeSpecifier.cpp \
../src/fml/type/UnionTypeSpecifier.cpp

CPP_DEPS += \
./src/fml/type/BaseSymbolTypeSpecifier.d \
./src/fml/type/BaseTypeSpecifier.d \
./src/fml/type/ChoiceTypeSpecifier.d \
./src/fml/type/ClassTypeSpecifier.d \
./src/fml/type/ContainerTypeSpecifier.d \
./src/fml/type/EnumTypeSpecifier.d \
./src/fml/type/IntervalTypeSpecifier.d \
./src/fml/type/TableOfTypeSpecifier.d \
./src/fml/type/TypeAliasSpecifier.d \
./src/fml/type/TypeManager.d \
./src/fml/type/TypeSpecifier.d \
./src/fml/type/UnionTypeSpecifier.d

OBJS += \
./src/fml/type/BaseSymbolTypeSpecifier.o \
./src/fml/type/BaseTypeSpecifier.o \
./src/fml/type/ChoiceTypeSpecifier.o \
./src/fml/type/ClassTypeSpecifier.o \
./src/fml/type/ContainerTypeSpecifier.o \
./src/fml/type/EnumTypeSpecifier.o \
./src/fml/type/IntervalTypeSpecifier.o \
./src/fml/type/TableOfTypeSpecifier.o \
./src/fml/type/TypeAliasSpecifier.o \
./src/fml/type/TypeManager.o \
./src/fml/type/TypeSpecifier.o \
./src/fml/type/UnionTypeSpecifier.o


# Each subdirectory must supply rules for building sources it contributes
src/fml/type/%.o: ../src/fml/type/%.cpp src/fml/type/subdir.mk
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -pipe -std=c++2a -D__AVM_LINUX__ -D_AVM_BUILTIN_NUMERIC_GMP_ -D_AVM_SOLVER_Z3_C_ -I"../src" -I"../third-party/include" -I"../third-party/include/antlr4-runtime" -O0 -Wall -c -fmessage-length=0  -Wsuggest-override   -Wsuggest-final-types   -Wsuggest-final-methods  -Wunused-local-typedefs -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


clean: clean-src-2f-fml-2f-type

clean-src-2f-fml-2f-type:
	-$(RM) ./src/fml/type/BaseSymbolTypeSpecifier.d ./src/fml/type/BaseSymbolTypeSpecifier.o ./src/fml/type/BaseTypeSpecifier.d ./src/fml/type/BaseTypeSpecifier.o ./src/fml/type/ChoiceTypeSpecifier.d ./src/fml/type/ChoiceTypeSpecifier.o ./src/fml/type/ClassTypeSpecifier.d ./src/fml/type/ClassTypeSpecifier.o ./src/fml/type/ContainerTypeSpecifier.d ./src/fml/type/ContainerTypeSpecifier.o ./src/fml/type/EnumTypeSpecifier.d ./src/fml/type/EnumTypeSpecifier.o ./src/fml/type/IntervalTypeSpecifier.d ./src/fml/type/IntervalTypeSpecifier.o ./src/fml/type/TableOfTypeSpecifier.d ./src/fml/type/TableOfTypeSpecifier.o ./src/fml/type/TypeAliasSpecifier.d ./src/fml/type/TypeAliasSpecifier.o ./src/fml/type/TypeManager.d ./src/fml/type/TypeManager.o ./src/fml/type/TypeSpecifier.d ./src/fml/type/TypeSpecifier.o ./src/fml/type/UnionTypeSpecifier.d ./src/fml/type/UnionTypeSpecifier.o

.PHONY: clean-src-2f-fml-2f-type

