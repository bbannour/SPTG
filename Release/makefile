################################################################################
# Automatically-generated file. Do not edit!
################################################################################

-include ../makefile.init

RM := rm -rf

# All of the sources participating in the build are defined here
-include sources.mk
-include src/util/subdir.mk
-include src/solver/api/subdir.mk
-include src/solver/subdir.mk
-include src/sew/subdir.mk
-include src/printer/subdir.mk
-include src/parser/sew/subdir.mk
-include src/parser/fml/subdir.mk
-include src/parser/subdir.mk
-include src/main/subdir.mk
-include src/fml/workflow/subdir.mk
-include src/fml/type/subdir.mk
-include src/fml/trace/subdir.mk
-include src/fml/template/subdir.mk
-include src/fml/symbol/subdir.mk
-include src/fml/runtime/subdir.mk
-include src/fml/operator/subdir.mk
-include src/fml/numeric/subdir.mk
-include src/fml/lib/subdir.mk
-include src/fml/infrastructure/subdir.mk
-include src/fml/expression/subdir.mk
-include src/fml/executable/subdir.mk
-include src/fml/common/subdir.mk
-include src/fml/builtin/subdir.mk
-include src/fml/buffer/subdir.mk
-include src/famsc/testing/subdir.mk
-include src/famsc/tcgenerator/subdir.mk
-include src/famsc/subdir.mk
-include src/famdv/coverage/subdir.mk
-include src/famdv/subdir.mk
-include src/famcore/trace/subdir.mk
-include src/famcore/serializer/subdir.mk
-include src/famcore/redundancy/subdir.mk
-include src/famcore/queue/subdir.mk
-include src/famcore/hitorjump/subdir.mk
-include src/famcore/debug/subdir.mk
-include src/famcore/api/subdir.mk
-include src/famcore/subdir.mk
-include src/computer/primitive/subdir.mk
-include src/computer/instruction/subdir.mk
-include src/computer/subdir.mk
-include src/common/subdir.mk
-include src/collection/subdir.mk
-include src/builder/primitive/subdir.mk
-include src/builder/compiler/subdir.mk
-include src/builder/analysis/subdir.mk
-include src/builder/subdir.mk
-include src/base/subdir.mk
ifneq ($(MAKECMDGOALS),clean)
ifneq ($(strip $(C++M_DEPS)),)
-include $(C++M_DEPS)
endif
ifneq ($(strip $(C++_DEPS)),)
-include $(C++_DEPS)
endif
ifneq ($(strip $(CCM_DEPS)),)
-include $(CCM_DEPS)
endif
ifneq ($(strip $(CC_DEPS)),)
-include $(CC_DEPS)
endif
ifneq ($(strip $(CPP_DEPS)),)
-include $(CPP_DEPS)
endif
ifneq ($(strip $(CXXM_DEPS)),)
-include $(CXXM_DEPS)
endif
ifneq ($(strip $(CXX_DEPS)),)
-include $(CXX_DEPS)
endif
ifneq ($(strip $(C_DEPS)),)
-include $(C_DEPS)
endif
ifneq ($(strip $(C_UPPER_DEPS)),)
-include $(C_UPPER_DEPS)
endif
endif

-include ../makefile.defs

OPTIONAL_TOOL_DEPS := \
$(wildcard ../makefile.defs) \
$(wildcard ../makefile.init) \
$(wildcard ../makefile.targets) \


BUILD_ARTIFACT_NAME := avm
BUILD_ARTIFACT_EXTENSION := exe
BUILD_ARTIFACT_PREFIX :=
BUILD_ARTIFACT := $(BUILD_ARTIFACT_PREFIX)$(BUILD_ARTIFACT_NAME)$(if $(BUILD_ARTIFACT_EXTENSION),.$(BUILD_ARTIFACT_EXTENSION),)

# Add inputs and outputs from these tool invocations to the build variables

# All Target
all:
	+@$(MAKE) --no-print-directory main-build && $(MAKE) --no-print-directory post-build

# Main-build Target
main-build: sptg.exe

# Tool invocations
sptg.exe: $(OBJS) $(USER_OBJS) makefile $(OPTIONAL_TOOL_DEPS)
	@echo 'Building target: $@'
	@echo 'Invoking: GCC C++ Linker'
	g++ -pipe -static -s -L"../third-party/lib" -Wl,--no-as-needed  -Wl,--as-needed -ldl -pthread -o "sptg.exe" $(OBJS) $(USER_OBJS) $(LIBS) -lantlr4-runtime -lz3 -lgmpxx -lgmp -lstdc++fs -lpthread
	@echo 'Finished building target: $@'
	@echo ' '

# Other Targets
clean:
	-$(RM) sptg.exe
	-@echo ' '

post-build:
	-cp -f sptg.exe ../bin/sptg.exe
	-@echo ' '

.PHONY: all clean dependents main-build post-build

-include ../makefile.targets
