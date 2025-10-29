 
GRAMMAR=fml

GENERATED=.

ANTLR3_PATTERN=Lexer Parser

GRAMMAR_FILES=$(addsuffix .g, $(GRAMMAR))

ANTLR3_GENERATED_STEM=$(addprefix $(GENERATED)/$(GRAMMAR), $(ANTLR3_PATTERN))

GENERATED_HEADERS=$(addsuffix .h  , $(ANTLR3_GENERATED_STEM))

GENERATED_SOURCES=$(addsuffix .c, $(ANTLR3_GENERATED_STEM))

GENERATED_TOKENS=$(addsuffix .tokens, $(ANTLR3_GENERATED_STEM))

GENERATED_FILES=$(GENERATED_HEADERS) $(GENERATED_SOURCES) $(GENERATED_TOKENS)

.precious: $(GENERATED_FILES)

ANTLR3_TARGET=$(GENERATED)/.antlr3_generated

ANTLR3_TOOL= java -jar ../../../third-party/antlr/antlr-3.4-complete.jar


all: antlr4  patch

antlr4: $(ANTLR3_TARGET)
	@echo "Generated files : $(GENERATED_FILES)"

$(ANTLR3_TARGET): $(GRAMMAR_FILES)
	$(ANTLR3_TOOL) -o $(GENERATED) $(GRAMMAR_FILES)
	@touch $(ANTLR3_TARGET)

patch: $(GENERATED_HEADERS)
	@echo "Patch $(GENERATED_HEADERS) ..."
	sed -i -z 's/\(\#ifdef __cplusplus\)\n\(extern "C" {\)\n\(\#endif\)/\/\/\1\n\/\/\2\n\/\/\3/g'  $(GENERATED_HEADERS)
	sed -i -z "s/\(\#ifdef __cplusplus\)\n\(\}\)\n\(\#endif\)/\/\/\1\n\/\/\2\n\/\/\3/g"  $(GENERATED_HEADERS)


force:
	$(ANTLR3_TOOL) -o $(GENERATED) $(GRAMMAR_FILES)
	@touch $(ANTLR3_TARGET)

#dirs:
#	mkdir -p $(GENERATED) 
#
#clean:
#	rm -rf $(GENERATED_FILES)
