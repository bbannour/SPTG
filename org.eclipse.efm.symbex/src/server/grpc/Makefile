#
# Copyright 2015 gRPC authors.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

HOST_SYSTEM = $(shell uname | cut -f 1 -d_)
SYSTEM ?= $(HOST_SYSTEM)
CXX = g++
CPPFLAGS += `pkg-config --cflags protobuf grpc`
CXXFLAGS += -std=c++20a


#MSYS2_ENV = mingw64
MSYS2_ENV = ucrt64

ifeq ($(SYSTEM),MINGW64)
LDFLAGS += -L/$(MSYS2_ENV)/lib -lgrpc++ -lprotobuf\
           -pthread\
           -Wl,--no-as-needed -lgrpc++_reflection -Wl,--as-needed\
           -ldl
else ifeq ($(SYSTEM),Linux)
LDFLAGS += -lgrpc++ -lprotobuf\
           -pthread\
           -Wl,--no-as-needed -lgrpc++_reflection -Wl,--as-needed\
           -ldl
else #ifeq ($(SYSTEM),Darwin)
LDFLAGS += -L/usr/lib `pkg-config --libs protobuf grpc++`\
           -pthread\
           -lgrpc++_reflection\
           -ldl
endif

PROTOC = protoc
GRPC_CPP_PLUGIN = grpc_cpp_plugin

ifeq ($(SYSTEM),MINGW64)
GRPC_CPP_PLUGIN_PATH = /$(MSYS2_ENV)/bin/grpc_cpp_plugin.exe
else
GRPC_CPP_PLUGIN_PATH ?= `which $(GRPC_CPP_PLUGIN)`
endif

# PROTOS_PATH = ../../protos
PROTOS_PATH = ./

vpath %.proto $(PROTOS_PATH)


CMD_SED = sed -i

GRPC_PB_FILE = SymbexServices.grpc.pb.cc
PB_FILE = SymbexServices.pb.cc

ADD_HEADER = '1i \#if defined(_EXPERIMENTAL_SERVER_GRPC_FEATURE_)\n'
ADD_FOOTER = '$$a \\n\#endif \/* _EXPERIMENTAL_SERVER_GRPC_FEATURE_ *\/'

all: info_sytem gen_grpc_pb_files gen_pb_files  patch_enabling_feature

info_sytem:
	@echo "The running system is $(SYSTEM)"
	
gen_grpc_pb_files: SymbexServices.proto
	$(PROTOC) -I $(PROTOS_PATH) --grpc_out=. --plugin=protoc-gen-grpc=$(GRPC_CPP_PLUGIN_PATH) $<

gen_pb_files: SymbexServices.proto
	$(PROTOC) -I $(PROTOS_PATH) --cpp_out=. $<

patch_enabling_feature:
	$(CMD_SED) $(ADD_HEADER)  $(GRPC_PB_FILE)
	$(CMD_SED) $(ADD_FOOTER)  $(GRPC_PB_FILE)
	$(CMD_SED) $(ADD_HEADER)  $(PB_FILE)
	$(CMD_SED) $(ADD_FOOTER)  $(PB_FILE)

clean:
	rm -f *.pb.cc *.pb.h


# The following is to test your system and ensure a smoother experience.
# They are by no means necessary to actually compile a grpc-enabled software.

PROTOC_CMD = which $(PROTOC)
PROTOC_CHECK_CMD = $(PROTOC) --version | grep -q libprotoc.3
PLUGIN_CHECK_CMD = which $(GRPC_CPP_PLUGIN)
HAS_PROTOC = $(shell $(PROTOC_CMD) > /dev/null && echo true || echo false)
ifeq ($(HAS_PROTOC),true)
HAS_VALID_PROTOC = $(shell $(PROTOC_CHECK_CMD) 2> /dev/null && echo true || echo false)
endif
HAS_PLUGIN = $(shell $(PLUGIN_CHECK_CMD) > /dev/null && echo true || echo false)

SYSTEM_OK = false
ifeq ($(HAS_VALID_PROTOC),true)
ifeq ($(HAS_PLUGIN),true)
SYSTEM_OK = true
endif
endif

system-check:
ifneq ($(HAS_VALID_PROTOC),true)
	@echo " DEPENDENCY ERROR"
	@echo
	@echo "You don't have protoc 3.0.0 installed in your path."
	@echo "Please install Google protocol buffers 3.0.0 and its compiler."
	@echo "You can find it here:"
	@echo
	@echo "   https://github.com/google/protobuf/releases/tag/v3.0.0"
	@echo
	@echo "Here is what I get when trying to evaluate your version of protoc:"
	@echo
	-$(PROTOC) --version
	@echo
	@echo
endif
ifneq ($(HAS_PLUGIN),true)
	@echo " DEPENDENCY ERROR"
	@echo
	@echo "You don't have the grpc c++ protobuf plugin installed in your path."
	@echo "Please install grpc. You can find it here:"
	@echo
	@echo "   https://github.com/grpc/grpc"
	@echo
	@echo "Here is what I get when trying to detect if you have the plugin:"
	@echo
	-which $(GRPC_CPP_PLUGIN)
	@echo
	@echo
endif
ifneq ($(SYSTEM_OK),true)
	@false
endif
