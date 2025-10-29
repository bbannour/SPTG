 
GRAMMAR=SEW

GENERATED=.

ANTLR4_PATTERN=Lexer Parser

GRAMMAR_FILES=$(addsuffix .g4, $(addprefix $(GRAMMAR), $(ANTLR4_PATTERN)))

ANTLR4_GENERATED_STEM=$(addprefix $(GENERATED)/$(GRAMMAR), $(ANTLR4_PATTERN))

GENERATED_HEADERS=$(addsuffix .h  , $(ANTLR4_GENERATED_STEM))

GENERATED_SOURCES=$(addsuffix .cpp, $(ANTLR4_GENERATED_STEM))

GENERATED_TOKENS=$(addsuffix .tokens, $(ANTLR4_GENERATED_STEM))

GENERATED_INTERP=$(addsuffix .interp, $(ANTLR4_GENERATED_STEM))

GENERATED_FILES=$(GENERATED_HEADERS) $(GENERATED_SOURCES) $(GENERATED_TOKENS) $(GENERATED_INTERP)

.precious: $(GENERATED_FILES)

ANTLR4_TARGET=$(GENERATED)/.antlr4_generated

#ANTLR4_OPTION=-Xforce-atn
#ANTLR4_OPTION+=-message-format gnu -Xlog

ANTLR4_TOOL=java -jar ../../../third-party/antlr/antlr-4.13.2-complete.jar $(ANTLR4_OPTION)

ANTLR4_CPP_OPTIONS=-Dlanguage=Cpp -no-listener -no-visitor

ANTLR4_CPP_TOOLING=$(ANTLR4_TOOL) $(ANTLR4_CPP_OPTIONS)


all: antlr4

antlr4: $(ANTLR4_TARGET)
	@echo "Generated files : $(GENERATED_FILES)"

$(ANTLR4_TARGET): $(GRAMMAR_FILES)
	$(ANTLR4_CPP_TOOLING) -package sep -o $(GENERATED) $(GRAMMAR_FILES)
	@touch $(ANTLR4_TARGET)

force:
	$(ANTLR4_CPP_TOOLING) -package sep -o $(GENERATED) $(GRAMMAR_FILES)
	@touch $(ANTLR4_TARGET)

#dirs:
#	mkdir -p $(GENERATED) 
#
#clean:
#	rm -rf $(GENERATED_FILES) $(ANTLR4_TARGET)
