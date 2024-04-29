
// Generated from FML.g4 by ANTLR 4.13.1

#pragma once


#include "antlr4-runtime.h"


namespace sep {


class  FMLLexer : public antlr4::Lexer {
public:
  enum {
    T__0 = 1, T__1 = 2, T__2 = 3, T__3 = 4, T__4 = 5, T__5 = 6, T__6 = 7, 
    T__7 = 8, T__8 = 9, T__9 = 10, T__10 = 11, T__11 = 12, T__12 = 13, T__13 = 14, 
    T__14 = 15, T__15 = 16, T__16 = 17, T__17 = 18, T__18 = 19, T__19 = 20, 
    T__20 = 21, T__21 = 22, T__22 = 23, T__23 = 24, T__24 = 25, T__25 = 26, 
    T__26 = 27, T__27 = 28, T__28 = 29, T__29 = 30, T__30 = 31, T__31 = 32, 
    T__32 = 33, T__33 = 34, T__34 = 35, T__35 = 36, T__36 = 37, T__37 = 38, 
    T__38 = 39, T__39 = 40, T__40 = 41, T__41 = 42, T__42 = 43, T__43 = 44, 
    T__44 = 45, T__45 = 46, T__46 = 47, T__47 = 48, T__48 = 49, T__49 = 50, 
    T__50 = 51, T__51 = 52, T__52 = 53, T__53 = 54, T__54 = 55, T__55 = 56, 
    T__56 = 57, T__57 = 58, T__58 = 59, T__59 = 60, T__60 = 61, T__61 = 62, 
    T__62 = 63, T__63 = 64, T__64 = 65, T__65 = 66, T__66 = 67, T__67 = 68, 
    T__68 = 69, T__69 = 70, T__70 = 71, T__71 = 72, T__72 = 73, T__73 = 74, 
    T__74 = 75, T__75 = 76, T__76 = 77, T__77 = 78, T__78 = 79, T__79 = 80, 
    T__80 = 81, T__81 = 82, T__82 = 83, T__83 = 84, T__84 = 85, T__85 = 86, 
    T__86 = 87, T__87 = 88, T__88 = 89, T__89 = 90, T__90 = 91, T__91 = 92, 
    T__92 = 93, T__93 = 94, T__94 = 95, T__95 = 96, T__96 = 97, T__97 = 98, 
    T__98 = 99, T__99 = 100, T__100 = 101, T__101 = 102, T__102 = 103, T__103 = 104, 
    T__104 = 105, T__105 = 106, T__106 = 107, T__107 = 108, T__108 = 109, 
    T__109 = 110, T__110 = 111, T__111 = 112, T__112 = 113, T__113 = 114, 
    T__114 = 115, T__115 = 116, T__116 = 117, T__117 = 118, T__118 = 119, 
    T__119 = 120, T__120 = 121, T__121 = 122, T__122 = 123, T__123 = 124, 
    T__124 = 125, T__125 = 126, T__126 = 127, T__127 = 128, T__128 = 129, 
    T__129 = 130, T__130 = 131, T__131 = 132, T__132 = 133, T__133 = 134, 
    T__134 = 135, T__135 = 136, T__136 = 137, T__137 = 138, T__138 = 139, 
    T__139 = 140, T__140 = 141, T__141 = 142, T__142 = 143, T__143 = 144, 
    T__144 = 145, T__145 = 146, T__146 = 147, T__147 = 148, T__148 = 149, 
    T__149 = 150, T__150 = 151, T__151 = 152, T__152 = 153, T__153 = 154, 
    T__154 = 155, T__155 = 156, T__156 = 157, T__157 = 158, T__158 = 159, 
    T__159 = 160, T__160 = 161, T__161 = 162, T__162 = 163, T__163 = 164, 
    T__164 = 165, T__165 = 166, T__166 = 167, T__167 = 168, T__168 = 169, 
    T__169 = 170, T__170 = 171, T__171 = 172, T__172 = 173, T__173 = 174, 
    T__174 = 175, T__175 = 176, T__176 = 177, T__177 = 178, T__178 = 179, 
    T__179 = 180, T__180 = 181, T__181 = 182, T__182 = 183, T__183 = 184, 
    T__184 = 185, T__185 = 186, T__186 = 187, T__187 = 188, T__188 = 189, 
    T__189 = 190, T__190 = 191, T__191 = 192, T__192 = 193, T__193 = 194, 
    T__194 = 195, T__195 = 196, T__196 = 197, T__197 = 198, T__198 = 199, 
    T__199 = 200, T__200 = 201, T__201 = 202, T__202 = 203, T__203 = 204, 
    T__204 = 205, T__205 = 206, T__206 = 207, T__207 = 208, T__208 = 209, 
    T__209 = 210, T__210 = 211, T__211 = 212, T__212 = 213, T__213 = 214, 
    T__214 = 215, T__215 = 216, T__216 = 217, T__217 = 218, T__218 = 219, 
    T__219 = 220, T__220 = 221, T__221 = 222, T__222 = 223, T__223 = 224, 
    T__224 = 225, T__225 = 226, T__226 = 227, T__227 = 228, T__228 = 229, 
    T__229 = 230, T__230 = 231, T__231 = 232, T__232 = 233, T__233 = 234, 
    T__234 = 235, T__235 = 236, T__236 = 237, T__237 = 238, T__238 = 239, 
    T__239 = 240, T__240 = 241, T__241 = 242, T__242 = 243, T__243 = 244, 
    T__244 = 245, T__245 = 246, T__246 = 247, T__247 = 248, T__248 = 249, 
    T__249 = 250, T__250 = 251, T__251 = 252, T__252 = 253, T__253 = 254, 
    T__254 = 255, T__255 = 256, T__256 = 257, T__257 = 258, T__258 = 259, 
    T__259 = 260, T__260 = 261, T__261 = 262, T__262 = 263, T__263 = 264, 
    T__264 = 265, T__265 = 266, T__266 = 267, T__267 = 268, T__268 = 269, 
    T__269 = 270, T__270 = 271, T__271 = 272, T__272 = 273, T__273 = 274, 
    T__274 = 275, T__275 = 276, T__276 = 277, T__277 = 278, T__278 = 279, 
    T__279 = 280, T__280 = 281, T__281 = 282, T__282 = 283, T__283 = 284, 
    T__284 = 285, T__285 = 286, T__286 = 287, T__287 = 288, T__288 = 289, 
    T__289 = 290, T__290 = 291, T__291 = 292, T__292 = 293, T__293 = 294, 
    T__294 = 295, T__295 = 296, T__296 = 297, T__297 = 298, T__298 = 299, 
    T__299 = 300, T__300 = 301, T__301 = 302, T__302 = 303, T__303 = 304, 
    T__304 = 305, T__305 = 306, T__306 = 307, T__307 = 308, T__308 = 309, 
    T__309 = 310, T__310 = 311, T__311 = 312, T__312 = 313, T__313 = 314, 
    T__314 = 315, T__315 = 316, T__316 = 317, OP_ATOMIC_SEQUENCE = 318, 
    OP_SEQUENCE = 319, OP_SEQUENCE_SIDE = 320, OP_SEQUENCE_WEAK = 321, OP_SCHEDULE_GT = 322, 
    OP_SCHEDULE_LT = 323, OP_SCHEDULE_XOR = 324, OP_SCHEDULE_AND_THEN = 325, 
    OP_SCHEDULE_OR_ELSE = 326, OP_NON_DETERMINISM = 327, OP_CONCURRENCY_ASYNC = 328, 
    OP_CONCURRENCY_AND = 329, OP_CONCURRENCY_OR = 330, OP_CONCURRENCY_INTERLEAVING = 331, 
    OP_CONCURRENCY_PARTIAL_ORDER = 332, OP_CONCURRENCY_PARALLEL = 333, OP_FORK = 334, 
    OP_JOIN = 335, OP_CONCURRENCY_RDV_ASYNC = 336, OP_CONCURRENCY_RDV_AND = 337, 
    OP_CONCURRENCY_RDV_OR = 338, OP_CONCURRENCY_RDV_INTERLEAVING = 339, 
    OP_CONCURRENCY_RDV_PARTIAL_ORDER = 340, OP_CONCURRENCY_RDV_PARALLEL = 341, 
    ASSIGN = 342, ASSIGN_AFTER = 343, ASSIGN_REF = 344, ASSIGN_MACRO = 345, 
    OP_PUSH = 346, OP_ASSIGN_TOP = 347, OP_TOP = 348, OP_POP = 349, LPAREN = 350, 
    RPAREN = 351, LCURLY = 352, RCURLY = 353, LBRACKET = 354, RBRACKET = 355, 
    LBRACKET_EXCEPT = 356, LPAREN_INVOKE = 357, LCURLY_INVOKE = 358, PERCENT_LPAREN_INVOKE = 359, 
    PERCENT_LPAREN = 360, RPAREN_PERCENT = 361, STATEMENT_PROMPT = 362, 
    DOLLAR_LCURLY = 363, RCURLY_DOLLAR = 364, PERCENT_LCURLY = 365, RCURLY_PERCENT = 366, 
    LBRACKET_BAR = 367, BAR_RBRACKET = 368, LBRACKET_LCURLY = 369, RCURLY_RBRACKET = 370, 
    COLON = 371, COMMA = 372, QUESTION = 373, SEMI = 374, DIESE = 375, DOLLAR = 376, 
    DOT = 377, DOTDOT = 378, COLONx2 = 379, LAND = 380, LAND_THEN = 381, 
    LAND_ASSIGN = 382, LAND_ASSIGN_AFTER = 383, LNOT = 384, LOR = 385, LOR_ELSE = 386, 
    LOR_ASSIGN = 387, LOR_ASSIGN_AFTER = 388, LXOR = 389, LIMPLIES = 390, 
    EQUAL = 391, NEQUAL = 392, SEQUAL = 393, NSEQUAL = 394, LTE = 395, LT_ = 396, 
    GTE = 397, GT = 398, PLUS = 399, PLUS_ASSIGN = 400, PLUS_ASSIGN_AFTER = 401, 
    INCR = 402, MINUS = 403, MINUS_ASSIGN = 404, MINUS_ASSIGN_AFTER = 405, 
    DECR = 406, STAR = 407, STAR_ASSIGN = 408, STAR_ASSIGN_AFTER = 409, 
    DIV = 410, DIV_ASSIGN = 411, DIV_ASSIGN_AFTER = 412, MOD = 413, MOD_ASSIGN = 414, 
    MOD_ASSIGN_AFTER = 415, RSHIFT = 416, RSHIFT_ASSIGN = 417, RSHIFT_ASSIGN_AFTER = 418, 
    LSHIFT = 419, LSHIFT_ASSIGN = 420, LSHIFT_ASSIGN_AFTER = 421, BAND = 422, 
    BAND_ASSIGN = 423, BAND_ASSIGN_AFTER = 424, BNOT = 425, BOR = 426, BOR_ASSIGN = 427, 
    BOR_ASSIGN_AFTER = 428, BXOR = 429, BXOR_ASSIGN = 430, BXOR_ASSIGN_AFTER = 431, 
    ID = 432, AT_ID = 433, StringLiteral = 434, CharLiteral = 435, FloatLiteral = 436, 
    RationalLiteral = 437, IntegerLiteral = 438, WHITESPACE = 439, NEWLINE = 440, 
    BLOCKCOMMENT = 441, LINECOMMENT = 442
  };

  explicit FMLLexer(antlr4::CharStream *input);

  ~FMLLexer() override;


  std::string getGrammarFileName() const override;

  const std::vector<std::string>& getRuleNames() const override;

  const std::vector<std::string>& getChannelNames() const override;

  const std::vector<std::string>& getModeNames() const override;

  const antlr4::dfa::Vocabulary& getVocabulary() const override;

  antlr4::atn::SerializedATNView getSerializedATN() const override;

  const antlr4::atn::ATN& getATN() const override;

  void action(antlr4::RuleContext *context, size_t ruleIndex, size_t actionIndex) override;

  // By default the static state used to implement the lexer is lazily initialized during the first
  // call to the constructor. You can call this function if you wish to initialize the static state
  // ahead of time.
  static void initialize();

private:

  // Individual action functions triggered by action() above.
  void AT_IDAction(antlr4::RuleContext *context, size_t actionIndex);
  void StringLiteralAction(antlr4::RuleContext *context, size_t actionIndex);
  void CharLiteralAction(antlr4::RuleContext *context, size_t actionIndex);

  // Individual semantic predicate functions triggered by sempred() above.

};

}  // namespace sep
