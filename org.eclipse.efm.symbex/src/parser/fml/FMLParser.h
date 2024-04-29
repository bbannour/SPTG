
/*******************************************************************************
 * Copyright (c) 2021 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and Implementation
 *******************************************************************************/
	
/* parser/listener/visitor header section */


// Generated from FML.g4 by ANTLR 4.13.1

#pragma once

/* parser precinclude section */
	
	#include <common/BF.h>
	
	#include <collection/BFContainer.h>
	
	#include <fml/common/BehavioralElement.h>
	#include <fml/common/ModifierElement.h>
	#include <fml/common/SpecifierElement.h>
	
	#include <fml/executable/ExecutableLib.h>
	
	#include <fml/expression/AvmCode.h>
	#include <fml/expression/BuiltinArray.h>
	#include <fml/expression/ExpressionConstant.h>
	#include <fml/expression/ExpressionConstructor.h>
	#include <fml/expression/StatementConstructor.h>
	
	#include <fml/lib/IComPoint.h>
	
	#include <fml/operator/Operator.h>
	#include <fml/operator/OperatorManager.h>
	
	#include <fml/template/TemplateFactory.h>
	
	#include <fml/type/TypeSpecifier.h>
	
	#include <fml/type/TypeManager.h>
	
	#include <fml/infrastructure/Buffer.h>
	#include <fml/infrastructure/Channel.h>
	#include <fml/infrastructure/ComPoint.h>
	#include <fml/infrastructure/ComProtocol.h>
	#include <fml/infrastructure/ComRoute.h>
	#include <fml/infrastructure/Connector.h>
	#include <fml/infrastructure/DataType.h>
	#include <fml/infrastructure/Machine.h>
	#include <fml/infrastructure/Package.h>
	#include <fml/infrastructure/Port.h>
	#include <fml/infrastructure/Routine.h>
	#include <fml/infrastructure/System.h>
	#include <fml/infrastructure/Transition.h>
	#include <fml/infrastructure/Variable.h>
	
	#include <fml/infrastructure/BehavioralPart.h>
	#include <fml/infrastructure/CompositePart.h>
	#include <fml/infrastructure/InstanceSpecifierPart.h>
	#include <fml/infrastructure/InteractionPart.h>
	#include <fml/infrastructure/ModelOfComputationPart.h>
	//#include <fml/infrastructure/PropertyPart.h>
	
	#include <fml/workflow/Query.h>
	#include <fml/workflow/UniFormIdentifier.h>
	#include <fml/workflow/WObject.h>

	#include <parser/ParserUtil.h>



#include "antlr4-runtime.h"


/* parser postinclude section */
#ifndef _WIN32
#pragma GCC diagnostic ignored "-Wunused-parameter"
#endif


namespace sep {

 /* parser context section */ 

class  FMLParser : public antlr4::Parser {
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

  enum {
    RuleFormalML = 0, RulePrologue_fml = 1, RulePrologue_attribute = 2, 
    RulePrologue_options = 3, RuleModifier_declaration = 4, RuleModifier_direction = 5, 
    RuleModifier_direction_text = 6, RuleModifier_set_direction_strict_text = 7, 
    RuleModifier_direction_symbol = 8, RuleModifier_param = 9, RuleProcedure_modifier_specifier = 10, 
    RuleExecutable_modifier_specifier = 11, RuleInstance_modifier_specifier = 12, 
    RuleModifier_transition = 13, RuleDef_package = 14, RuleDef_system = 15, 
    RuleQualifiedNameID = 16, RuleInteger_constant = 17, RuleFloat_constant = 18, 
    RuleSection_header = 19, RuleSection_import = 20, RuleInclude_package = 21, 
    RuleSection_procedure = 22, RuleDef_procedure = 23, RuleDef_machine_parameters = 24, 
    RuleDef_machine_variable_parameter_atom = 25, RuleDef_machine_returns = 26, 
    RuleDef_machine_variable_return_atom = 27, RuleDef_body_procedure = 28, 
    RuleDef_body_procedure_section = 29, RuleDef_body_procedure_simplif = 30, 
    RuleSection_composite_structure = 31, RuleSection_composite_generic = 32, 
    RuleSection_machine_model = 33, RuleSection_machine_prototype = 34, 
    RuleSection_machine_instance = 35, RuleExecutable_machine = 36, RuleExecutable_model_definiton = 37, 
    RuleExecutable_instance_definiton = 38, RuleDecl_instance = 39, RuleDef_instance_on_new_activity = 40, 
    RuleDef_instance_on_new_activity_parameter = 41, RuleOp_assign_param = 42, 
    RuleDef_instance_activity = 43, RuleSection_behavior = 44, RuleDef_instance_count = 45, 
    RuleDef_instance_count_atom = 46, RuleDef_machine = 47, RuleDef_body_machine = 48, 
    RuleDef_body_machine_section = 49, RuleDef_body_machine_simplif = 50, 
    RuleAny_def_statemachine = 51, RuleDef_statemachine = 52, RuleDef_body_statemachine = 53, 
    RuleSection_state_region = 54, RuleSection_composite_region = 55, RuleSection_statemachine = 56, 
    RuleDef_state = 57, RuleState_kw_id = 58, RuleState_id = 59, RuleDef_state_singleton = 60, 
    RuleExecutable_specifier = 61, RuleExecutable_specifier_atom = 62, RuleInstance_machine_model = 63, 
    RuleDef_body_state = 64, RuleDef_body_state_section = 65, RuleDef_body_state_simplif = 66, 
    RuleSection_transition = 67, RuleDef_transition = 68, RuleKind_transition = 69, 
    RuleMoc_transition_attribute = 70, RuleMoc_transition = 71, RuleMoc_transition_atom = 72, 
    RuleMoe_transition = 73, RuleTransition_statement = 74, RuleTransition_trigger = 75, 
    RuleTransition_guard = 76, RuleTransition_timed_guard = 77, RuleTransition_effect = 78, 
    RuleTarget_state_id = 79, RuleTarget_state_kw_id = 80, RuleDef_state_activity = 81, 
    RuleSection_header_import_parameter_property = 82, RuleSection_parameter = 83, 
    RuleSection_property = 84, RuleSection_property_free_declaration = 85, 
    RuleProperty_declaration = 86, RuleDecl_property_element = 87, RuleLabelled_argument = 88, 
    RuleDecl_instance_machine_params = 89, RuleDecl_instance_machine_returns = 90, 
    RuleActivity_machine_param_return = 91, RuleDecl_port = 92, RuleDecl_port_impl = 93, 
    RuleDecl_signal = 94, RuleDecl_signal_impl = 95, RuleTyped_parameter_input = 96, 
    RuleTyped_parameter_return = 97, RuleTyped_parameter_atom = 98, RuleDecl_buffer = 99, 
    RuleDecl_buffer_impl = 100, RuleDef_buffer = 101, RulePolicy_buffer = 102, 
    RuleRef_buffer = 103, RuleInitial_buffer_contents = 104, RuleDecl_channel = 105, 
    RuleDecl_channel_port = 106, RuleDecl_channel_var = 107, RuleDecl_function = 108, 
    RuleDecl_function_impl = 109, RuleDecl_variable = 110, RuleDecl_variable_time_clock_impl = 111, 
    RuleDecl_variable_impl = 112, RuleDecl_variable_atom_impl = 113, RuleDecl_typed_variable_atom_impl = 114, 
    RuleInitial_value = 115, RuleType_var = 116, RuleDef_type_array = 117, 
    RuleDef_type_array_size = 118, RuleDef_type_container = 119, RuleSpecifier_buffer = 120, 
    RuleDef_type_interval = 121, RuleBase_type_var = 122, RulePrimitive_type = 123, 
    RuleBit_field_size = 124, RuleString_field_size = 125, RuleRange_constant = 126, 
    RuleOn_write_var_routine_def = 127, RuleVar_routine_def = 128, RuleRoutine_single_param = 129, 
    RuleDef_enum = 130, RuleDef_enum_impl = 131, RuleDef_struct = 132, RuleDef_class_structure_impl = 133, 
    RuleDef_choice = 134, RuleDef_choice_impl = 135, RuleDef_union = 136, 
    RuleDef_union_impl = 137, RuleDef_type = 138, RuleDef_type_impl = 139, 
    RuleDef_type_atom_impl = 140, RuleDef_typedef_constraint = 141, RuleTime_type = 142, 
    RuleTime_clock_type = 143, RuleTime_type_domain = 144, RuleSection_model_of_computation = 145, 
    RuleSection_routine = 146, RuleDef_routine_model = 147, RuleDef_routine_model_impl = 148, 
    RuleDef_routine_parameters = 149, RuleDef_routine_param_atom = 150, 
    RuleDef_routine_returns = 151, RuleDef_routine_returns_atom = 152, RuleSection_model_of_execution = 153, 
    RuleDef_moe_primitive = 154, RuleDef_routine_seq = 155, RuleSection_model_of_interaction = 156, 
    RuleCom_protocol = 157, RuleCom_cast = 158, RuleBuffer_com = 159, RuleCom_connector = 160, 
    RuleCom_route = 161, RuleCom_route_points = 162, RuleCom_port = 163, 
    RuleCom_port_id = 164, RuleStatement = 165, RuleBlock_statement = 166, 
    RuleOp_block = 167, RuleOp_sequence = 168, RuleOp_scheduling = 169, 
    RuleOp_concurrency = 170, RuleOp_invokable = 171, RulePrefix_statement = 172, 
    RulePrefix_expression = 173, RuleAvm_operator = 174, RuleStatement_invoke_method = 175, 
    RuleStatement_invoke = 176, RuleExpression_invoke = 177, RuleStatement_activity_new = 178, 
    RuleDecl_instance_dynamic_impl = 179, RuleExpression_activity_new = 180, 
    RuleStatement_prompt = 181, RuleStatement_prompt_obs = 182, RuleStatement_prompt_obs_com = 183, 
    RuleMeta_statement = 184, RuleStatement_assign = 185, RuleLvalue = 186, 
    RuleParameters = 187, RuleStatement_com = 188, RuleStatement_com_input = 189, 
    RuleStatement_com_output = 190, RuleParameters_port = 191, RuleExpression_com = 192, 
    RuleStatement_constraint = 193, RuleStatement_guard = 194, RuleStatement_timed_guard = 195, 
    RuleStatement_checksat = 196, RuleExpression_checksat = 197, RuleExpression_quantifier = 198, 
    RuleStatement_ite = 199, RuleExpression_ite = 200, RuleStatement_iteration = 201, 
    RuleFor_assign_header = 202, RuleStatement_jump = 203, RuleExpression_lambda = 204, 
    RuleExpression_status = 205, RuleOp_activity = 206, RuleStatement_activity = 207, 
    RuleStatement_init_flow = 208, RuleStatement_invoke_routine = 209, RuleInvoke_routine_params = 210, 
    RuleInvoke_routine_returns = 211, RuleStatement_moc = 212, RuleExpression = 213, 
    RuleConditionalExpression = 214, RuleScheduleExpression = 215, RuleConditionalOrExpression = 216, 
    RuleConditionalImpliesExpression = 217, RuleConditionalAndExpression = 218, 
    RuleBitwiseOrExpression = 219, RuleBitwiseXorExpression = 220, RuleBitwiseAndExpression = 221, 
    RuleEqualityExpression = 222, RuleEqualOp = 223, RuleRelationalExpression = 224, 
    RuleRelationalOp = 225, RuleShiftExpression = 226, RuleShiftOp = 227, 
    RuleAdditiveExpression = 228, RuleMultiplicativeExpression = 229, RuleUnaryExpression = 230, 
    RuleCtorExpression = 231, RuleQuote_expression = 232, RuleMeta_eval_expression = 233, 
    RulePrimary = 234, RulePrimary_ufid = 235, RulePrimary_ufi = 236, RulePrimary_invoke = 237, 
    RuleLiteral = 238, RuleCollection_of_expression = 239
  };

  explicit FMLParser(antlr4::TokenStream *input);

  FMLParser(antlr4::TokenStream *input, const antlr4::atn::ParserATNSimulatorOptions &options);

  ~FMLParser() override;

  std::string getGrammarFileName() const override;

  const antlr4::atn::ATN& getATN() const override;

  const std::vector<std::string>& getRuleNames() const override;

  const antlr4::dfa::Vocabulary& getVocabulary() const override;

  antlr4::atn::SerializedATNView getSerializedATN() const override;


  /* public parser declarations/members section */

  	/**
  	 * GETTER - SETTER
  	 * mFilename
  	 */
  	inline const std::string & getFilename() const
  	{
  		return mFilename;
  	}
  	
  	inline void setFilename(const std::string & aFilename)
  	{
  		mFilename = aFilename;
  	}

  	/**
  	 * GETTER - SETTER
  	 * noOfErrors
  	 */
  	inline std::size_t hasError()
  	{
  		return( numberOfErrors() > 0 );
  	}

  	inline std::size_t numberOfErrors()
  	{
  		return( noOfErrors + getNumberOfSyntaxErrors() );
  	}

  	inline void resetErrors()
  	{
  		noOfErrors = 0;
  	}

  //	static const std::string versionInfo()
  //	{
  //		static std::string   info = "$ Id: FML.g, v 1.0 2021/10/29 Lapitre $";
  //
  //		return info;
  //	}


  	void reportError( const std::string & errorMessage )
  	{
  		reportMessage( errorMessage );
  		++noOfErrors;
  	}

  //	void reportError( const antlr::RecognitionException & ex )
  //	{
  //		AVM_OS_CERR << std::endl << ex.toString().c_str();
  //		++noOfErrors;
  //	}

  	void reportMessage( const std::string & message )
  	{
  		if( getFilename().length() > 0 )
  		{
  			AVM_OS_CERR << getFilename() << ":";
  		}

  		AVM_OS_CERR << getCurrentToken()->getLine() << ":"
  				<< getCurrentToken()->getCharPositionInLine()
  				<< " [error] " << message << std::endl;
  	}


  	void setLocation(WObject * wfObject, int bLine, int eLine,
  			int bOffset, int eOffset)
  	{
  		wfObject->setLocation(getFilename(), bLine, eLine);
  	}

  	void setLocation(TraceableElement & aTraceableElement, int bLine, int eLine,
  			int bOffset, int eOffset)
  	{
  		aTraceableElement.setLocation(getFilename(), bLine, eLine);
  	}

  	void setLocation(TraceableElement * aTraceableElement, int bLine, int eLine,
  			int bOffset, int eOffset)
  	{
  		aTraceableElement->setLocation(getFilename(), bLine, eLine);
  	}


  	void setLocation(TraceableElement * aTraceableElement, int bLine, int eLine)
  	{
  		aTraceableElement->setLocation(getFilename(), bLine, eLine);
  	}


  	int getNextTokenLine()
  	{
  		return( getCurrentToken()->getLine() );
  	}

  	int getNextTokenStartIndex()
  	{
  		return 1;//( getCurrentToken(1).getLine() );
  	}

  	int getNextTokenStopIndex()
  	{
  		return 1;//( getCurrentToken().getLine() );
  	}


  	void addElement(WObject * wfContainer, WObject * wfObject)
  	{
  		if( (wfContainer != WObject::_NULL_) && (wfObject != WObject::_NULL_) )
  		{
  			wfContainer->append( wfObject );
  		}
  	}


  	////////////////////////////////////////////////////////////////////////////
  	// PARSER GLOBAL VARIABLE
  	////////////////////////////////////////////////////////////////////////////
  	
  	// WObject Manager
  	sep::WObjectManager * mWObjectManager = nullptr;
  	
  	// Current Parse System
  	sep::System * _SYSTEM_ = nullptr;
  	
  	// Current Parse Machine
  	sep::Machine * _CPM_ = nullptr;
  	
  	#define PUSH_CTX_CPM( cpm )   sep::ParserUtil::pushCTX( _CPM_ = cpm )
  	
  	#define PUSH_CTX_NEW( cpm )   sep::ParserUtil::pushDynamicCTX( _CPM_ = cpm )
  	
  	
  	// Current Parse Routine
  	sep::Routine * _CPR_ = nullptr;
  	
  	#define PUSH_CTX_CPR( cpr )   sep::ParserUtil::pushCTX( _CPR_ = cpr )
  	
  	// Current Parse Local PropertyPart
  	#define PUSH_CTX_LOCAL( cpl )   sep::ParserUtil::pushCTX( cpl )
  	
  	
  	// Pop old local parse context & update current machine & routine
  	#define POP_CTX               sep::ParserUtil::popCTX( _CPM_ , _CPR_ )
  	
  	#define POP_CTX_IF( cpm )   \
  			if( _CPM_ == cpm ) { sep::ParserUtil::popCTX( _CPM_ , _CPR_ ); }
  	
  	// Current Parse Routine | Machine | System
  	#define _CPRMS_  ( ( _CPR_ != nullptr )  \
  			? static_cast< sep::BehavioralElement * >(_CPR_)  \
  			: ( ( _CPM_ != nullptr )  \
  					? static_cast< sep::BehavioralElement * >(_CPM_)  \
  					: static_cast< sep::BehavioralElement * >(_SYSTEM_) ) )
  	
  	
  	// Current Parse [ [ Fully ] Qualified ] Name ID
  	std::string cpLOCATOR;
  	std::vector< std::string > cpQNID;
  	
  	
  	////////////////////////////////////////////////////////////////////////////
  	// DEFAULT STATE  #final, #terminal, #return
  	////////////////////////////////////////////////////////////////////////////
  	
  	sep::ListOfMachine needDefaultStateFinal;
  	
  	sep::ListOfMachine needDefaultStateTerminal;
  	
  	sep::ListOfMachine needDefaultStateReturn;
  	
  	
  	////////////////////////////////////////////////////////////////////////////
  	// TRANSITION ID
  	////////////////////////////////////////////////////////////////////////////
  	
  	std::size_t transition_id = 0;
  	
  	void resetTransitionID()
  	{
  		transition_id = 0;
  	}
  	
  	std::string newTransitionID(
  			const std::string & id, const std::string & prefix = "t")
  	{
  		return( id.empty() ?
  				(sep::OSS() << prefix << sep::NamedElement::NAME_ID_SEPARATOR
  							<< transition_id++).str() : id );
  	}
  	
  	
  	int mInvokeNewInstanceCount = 0;
  	
  	std::string newInvokeNewInstanceNameID(
  			sep::Machine * container, const std::string modelNameID)
  	{
  		return( sep::OSS() << modelNameID << sep::NamedElement::NAME_ID_SEPARATOR
  							<< mInvokeNewInstanceCount++ );
  	}
  	
  	
  	
  	int mProcedureCallCount = 0;
  	
  	
  	
  	////////////////////////////////////////////////////////////////////////////
  	// BUFFER ID
  	////////////////////////////////////////////////////////////////////////////
  	
  	std::size_t buffer_id = 0;
  	
  	void resetBufferID()
  	{
  		buffer_id = 0;
  	}
  	
  	std::string newBufferID(const std::string & prefix = sep::Buffer::ANONYM_ID)
  	{
  		return( sep::OSS() << prefix << sep::NamedElement::NAME_ID_SEPARATOR
  						<< buffer_id++ );
  	}
  	
  	
  	////////////////////////////////////////////////////////////////////////////
  	// CONNECTOR ID
  	////////////////////////////////////////////////////////////////////////////
  	
  	std::size_t connector_id = 0;
  	
  	void resetConnectorID()
  	{
  		connector_id = 0;
  	}
  	
  	std::string newConnectorID(const std::string & id,
  			const std::string & prefix = sep::Connector::ANONYM_ID)
  	{
  		return( id.empty() ?
  				(sep::OSS() << prefix << sep::NamedElement::NAME_ID_SEPARATOR
  							<< connector_id++).str() : id );
  	}
  	
  	////////////////////////////////////////////////////////////////////////////
  	// EXPRESSION UTILS
  	////////////////////////////////////////////////////////////////////////////

  	sep::BF new_uminus_expr(sep::BF & arg)
  	{
  		if( arg.isNumeric() )
  		{
  			return( sep::ExpressionConstructor::uminusExpr(arg) );
  		}
  		return( sep::ExpressionConstructor::newCode(
  				sep::OperatorManager::OPERATOR_UMINUS, arg) );
  	}
  	
  	sep::BF new_not_expr(sep::BF & arg)
  	{
  		if( arg.isBoolean() )
  		{
  			return( sep::ExpressionConstructor::notExpr(arg) );
  		}
  		return( sep::ExpressionConstructor::newCode(
  				sep::OperatorManager::OPERATOR_NOT, arg) );
  	}	
  		


  class FormalMLContext;
  class Prologue_fmlContext;
  class Prologue_attributeContext;
  class Prologue_optionsContext;
  class Modifier_declarationContext;
  class Modifier_directionContext;
  class Modifier_direction_textContext;
  class Modifier_set_direction_strict_textContext;
  class Modifier_direction_symbolContext;
  class Modifier_paramContext;
  class Procedure_modifier_specifierContext;
  class Executable_modifier_specifierContext;
  class Instance_modifier_specifierContext;
  class Modifier_transitionContext;
  class Def_packageContext;
  class Def_systemContext;
  class QualifiedNameIDContext;
  class Integer_constantContext;
  class Float_constantContext;
  class Section_headerContext;
  class Section_importContext;
  class Include_packageContext;
  class Section_procedureContext;
  class Def_procedureContext;
  class Def_machine_parametersContext;
  class Def_machine_variable_parameter_atomContext;
  class Def_machine_returnsContext;
  class Def_machine_variable_return_atomContext;
  class Def_body_procedureContext;
  class Def_body_procedure_sectionContext;
  class Def_body_procedure_simplifContext;
  class Section_composite_structureContext;
  class Section_composite_genericContext;
  class Section_machine_modelContext;
  class Section_machine_prototypeContext;
  class Section_machine_instanceContext;
  class Executable_machineContext;
  class Executable_model_definitonContext;
  class Executable_instance_definitonContext;
  class Decl_instanceContext;
  class Def_instance_on_new_activityContext;
  class Def_instance_on_new_activity_parameterContext;
  class Op_assign_paramContext;
  class Def_instance_activityContext;
  class Section_behaviorContext;
  class Def_instance_countContext;
  class Def_instance_count_atomContext;
  class Def_machineContext;
  class Def_body_machineContext;
  class Def_body_machine_sectionContext;
  class Def_body_machine_simplifContext;
  class Any_def_statemachineContext;
  class Def_statemachineContext;
  class Def_body_statemachineContext;
  class Section_state_regionContext;
  class Section_composite_regionContext;
  class Section_statemachineContext;
  class Def_stateContext;
  class State_kw_idContext;
  class State_idContext;
  class Def_state_singletonContext;
  class Executable_specifierContext;
  class Executable_specifier_atomContext;
  class Instance_machine_modelContext;
  class Def_body_stateContext;
  class Def_body_state_sectionContext;
  class Def_body_state_simplifContext;
  class Section_transitionContext;
  class Def_transitionContext;
  class Kind_transitionContext;
  class Moc_transition_attributeContext;
  class Moc_transitionContext;
  class Moc_transition_atomContext;
  class Moe_transitionContext;
  class Transition_statementContext;
  class Transition_triggerContext;
  class Transition_guardContext;
  class Transition_timed_guardContext;
  class Transition_effectContext;
  class Target_state_idContext;
  class Target_state_kw_idContext;
  class Def_state_activityContext;
  class Section_header_import_parameter_propertyContext;
  class Section_parameterContext;
  class Section_propertyContext;
  class Section_property_free_declarationContext;
  class Property_declarationContext;
  class Decl_property_elementContext;
  class Labelled_argumentContext;
  class Decl_instance_machine_paramsContext;
  class Decl_instance_machine_returnsContext;
  class Activity_machine_param_returnContext;
  class Decl_portContext;
  class Decl_port_implContext;
  class Decl_signalContext;
  class Decl_signal_implContext;
  class Typed_parameter_inputContext;
  class Typed_parameter_returnContext;
  class Typed_parameter_atomContext;
  class Decl_bufferContext;
  class Decl_buffer_implContext;
  class Def_bufferContext;
  class Policy_bufferContext;
  class Ref_bufferContext;
  class Initial_buffer_contentsContext;
  class Decl_channelContext;
  class Decl_channel_portContext;
  class Decl_channel_varContext;
  class Decl_functionContext;
  class Decl_function_implContext;
  class Decl_variableContext;
  class Decl_variable_time_clock_implContext;
  class Decl_variable_implContext;
  class Decl_variable_atom_implContext;
  class Decl_typed_variable_atom_implContext;
  class Initial_valueContext;
  class Type_varContext;
  class Def_type_arrayContext;
  class Def_type_array_sizeContext;
  class Def_type_containerContext;
  class Specifier_bufferContext;
  class Def_type_intervalContext;
  class Base_type_varContext;
  class Primitive_typeContext;
  class Bit_field_sizeContext;
  class String_field_sizeContext;
  class Range_constantContext;
  class On_write_var_routine_defContext;
  class Var_routine_defContext;
  class Routine_single_paramContext;
  class Def_enumContext;
  class Def_enum_implContext;
  class Def_structContext;
  class Def_class_structure_implContext;
  class Def_choiceContext;
  class Def_choice_implContext;
  class Def_unionContext;
  class Def_union_implContext;
  class Def_typeContext;
  class Def_type_implContext;
  class Def_type_atom_implContext;
  class Def_typedef_constraintContext;
  class Time_typeContext;
  class Time_clock_typeContext;
  class Time_type_domainContext;
  class Section_model_of_computationContext;
  class Section_routineContext;
  class Def_routine_modelContext;
  class Def_routine_model_implContext;
  class Def_routine_parametersContext;
  class Def_routine_param_atomContext;
  class Def_routine_returnsContext;
  class Def_routine_returns_atomContext;
  class Section_model_of_executionContext;
  class Def_moe_primitiveContext;
  class Def_routine_seqContext;
  class Section_model_of_interactionContext;
  class Com_protocolContext;
  class Com_castContext;
  class Buffer_comContext;
  class Com_connectorContext;
  class Com_routeContext;
  class Com_route_pointsContext;
  class Com_portContext;
  class Com_port_idContext;
  class StatementContext;
  class Block_statementContext;
  class Op_blockContext;
  class Op_sequenceContext;
  class Op_schedulingContext;
  class Op_concurrencyContext;
  class Op_invokableContext;
  class Prefix_statementContext;
  class Prefix_expressionContext;
  class Avm_operatorContext;
  class Statement_invoke_methodContext;
  class Statement_invokeContext;
  class Expression_invokeContext;
  class Statement_activity_newContext;
  class Decl_instance_dynamic_implContext;
  class Expression_activity_newContext;
  class Statement_promptContext;
  class Statement_prompt_obsContext;
  class Statement_prompt_obs_comContext;
  class Meta_statementContext;
  class Statement_assignContext;
  class LvalueContext;
  class ParametersContext;
  class Statement_comContext;
  class Statement_com_inputContext;
  class Statement_com_outputContext;
  class Parameters_portContext;
  class Expression_comContext;
  class Statement_constraintContext;
  class Statement_guardContext;
  class Statement_timed_guardContext;
  class Statement_checksatContext;
  class Expression_checksatContext;
  class Expression_quantifierContext;
  class Statement_iteContext;
  class Expression_iteContext;
  class Statement_iterationContext;
  class For_assign_headerContext;
  class Statement_jumpContext;
  class Expression_lambdaContext;
  class Expression_statusContext;
  class Op_activityContext;
  class Statement_activityContext;
  class Statement_init_flowContext;
  class Statement_invoke_routineContext;
  class Invoke_routine_paramsContext;
  class Invoke_routine_returnsContext;
  class Statement_mocContext;
  class ExpressionContext;
  class ConditionalExpressionContext;
  class ScheduleExpressionContext;
  class ConditionalOrExpressionContext;
  class ConditionalImpliesExpressionContext;
  class ConditionalAndExpressionContext;
  class BitwiseOrExpressionContext;
  class BitwiseXorExpressionContext;
  class BitwiseAndExpressionContext;
  class EqualityExpressionContext;
  class EqualOpContext;
  class RelationalExpressionContext;
  class RelationalOpContext;
  class ShiftExpressionContext;
  class ShiftOpContext;
  class AdditiveExpressionContext;
  class MultiplicativeExpressionContext;
  class UnaryExpressionContext;
  class CtorExpressionContext;
  class Quote_expressionContext;
  class Meta_eval_expressionContext;
  class PrimaryContext;
  class Primary_ufidContext;
  class Primary_ufiContext;
  class Primary_invokeContext;
  class LiteralContext;
  class Collection_of_expressionContext; 

  class  FormalMLContext : public antlr4::ParserRuleContext {
  public:
    sep::WObjectManager * aWObjectManager;
    sep::System * spec = nullptr;
    FMLParser::Prologue_fmlContext *pfml = nullptr;
    FMLParser::Def_systemContext *s = nullptr;
    FormalMLContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    FormalMLContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::WObjectManager * aWObjectManager);
    virtual size_t getRuleIndex() const override;
    Prologue_fmlContext *prologue_fml();
    Def_systemContext *def_system();

   
  };

  FormalMLContext* formalML(sep::WObjectManager * aWObjectManager);

  class  Prologue_fmlContext : public antlr4::ParserRuleContext {
  public:
    sep::WObject * fmlProlog = sep::WObject::_NULL_;
    antlr4::Token *id = nullptr;
    Prologue_fmlContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LT_();
    antlr4::tree::TerminalNode *GT();
    antlr4::tree::TerminalNode *COLON();
    std::vector<antlr4::tree::TerminalNode *> ID();
    antlr4::tree::TerminalNode* ID(size_t i);
    antlr4::tree::TerminalNode *ASSIGN();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    Prologue_attributeContext *prologue_attribute();
    Prologue_optionsContext *prologue_options();
    std::vector<antlr4::tree::TerminalNode *> FloatLiteral();
    antlr4::tree::TerminalNode* FloatLiteral(size_t i);
    std::vector<antlr4::tree::TerminalNode *> StringLiteral();
    antlr4::tree::TerminalNode* StringLiteral(size_t i);

   
  };

  Prologue_fmlContext* prologue_fml();

  class  Prologue_attributeContext : public antlr4::ParserRuleContext {
  public:
    sep::WObject * fmlProlog;
    antlr4::Token *id = nullptr;
    Prologue_attributeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Prologue_attributeContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::WObject * fmlProlog);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ASSIGN();
    antlr4::tree::TerminalNode *SEMI();
    antlr4::tree::TerminalNode *ID();

   
  };

  Prologue_attributeContext* prologue_attribute(sep::WObject * fmlProlog);

  class  Prologue_optionsContext : public antlr4::ParserRuleContext {
  public:
    antlr4::Token *id = nullptr;
    FMLParser::ExpressionContext *e = nullptr;
    Prologue_optionsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LCURLY();
    antlr4::tree::TerminalNode *RCURLY();
    std::vector<antlr4::tree::TerminalNode *> ASSIGN();
    antlr4::tree::TerminalNode* ASSIGN(size_t i);
    std::vector<antlr4::tree::TerminalNode *> SEMI();
    antlr4::tree::TerminalNode* SEMI(size_t i);
    std::vector<antlr4::tree::TerminalNode *> ID();
    antlr4::tree::TerminalNode* ID(size_t i);
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);

   
  };

  Prologue_optionsContext* prologue_options();

  class  Modifier_declarationContext : public antlr4::ParserRuleContext {
  public:
    sep::Modifier mdfr;
    Modifier_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Modifier_set_direction_strict_textContext *> modifier_set_direction_strict_text();
    Modifier_set_direction_strict_textContext* modifier_set_direction_strict_text(size_t i);

   
  };

  Modifier_declarationContext* modifier_declaration();

  class  Modifier_directionContext : public antlr4::ParserRuleContext {
  public:
    sep::Modifier mdfr;
    Modifier_directionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ASSIGN_REF();
    antlr4::tree::TerminalNode *LTE();

   
  };

  Modifier_directionContext* modifier_direction();

  class  Modifier_direction_textContext : public antlr4::ParserRuleContext {
  public:
    sep::Modifier mdfr;
    Modifier_direction_textContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;

   
  };

  Modifier_direction_textContext* modifier_direction_text();

  class  Modifier_set_direction_strict_textContext : public antlr4::ParserRuleContext {
  public:
    sep::Modifier * mdfr;
    Modifier_set_direction_strict_textContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Modifier_set_direction_strict_textContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Modifier * mdfr);
    virtual size_t getRuleIndex() const override;

   
  };

  Modifier_set_direction_strict_textContext* modifier_set_direction_strict_text(sep::Modifier * mdfr);

  class  Modifier_direction_symbolContext : public antlr4::ParserRuleContext {
  public:
    sep::Modifier mdfr;
    Modifier_direction_symbolContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ASSIGN_REF();
    antlr4::tree::TerminalNode *LTE();

   
  };

  Modifier_direction_symbolContext* modifier_direction_symbol();

  class  Modifier_paramContext : public antlr4::ParserRuleContext {
  public:
    sep::Modifier mdfr;
    FMLParser::Modifier_directionContext *m = nullptr;
    Modifier_paramContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Modifier_directionContext *modifier_direction();
    antlr4::tree::TerminalNode *BAND();

   
  };

  Modifier_paramContext* modifier_param();

  class  Procedure_modifier_specifierContext : public antlr4::ParserRuleContext {
  public:
    sep::Modifier mdfr;
    sep::Specifier spcfr;
    Procedure_modifier_specifierContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;

   
  };

  Procedure_modifier_specifierContext* procedure_modifier_specifier();

  class  Executable_modifier_specifierContext : public antlr4::ParserRuleContext {
  public:
    sep::Modifier mdfr;
    sep::Specifier spcfr;
    Executable_modifier_specifierContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;

   
  };

  Executable_modifier_specifierContext* executable_modifier_specifier();

  class  Instance_modifier_specifierContext : public antlr4::ParserRuleContext {
  public:
    sep::Modifier mdfr;
    sep::Specifier spcfr;
    Instance_modifier_specifierContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;

   
  };

  Instance_modifier_specifierContext* instance_modifier_specifier();

  class  Modifier_transitionContext : public antlr4::ParserRuleContext {
  public:
    sep::Modifier mdfr;
    sep::Specifier spcfr;
    Modifier_transitionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;

   
  };

  Modifier_transitionContext* modifier_transition();

  class  Def_packageContext : public antlr4::ParserRuleContext {
  public:
    sep::Package * pack;
    antlr4::Token *id = nullptr;
    antlr4::Token *stringliteralToken = nullptr;
    Def_packageContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LCURLY();
    antlr4::tree::TerminalNode *RCURLY();
    antlr4::tree::TerminalNode *ID();
    antlr4::tree::TerminalNode *StringLiteral();
    Section_headerContext *section_header();
    Section_importContext *section_import();
    std::vector<Section_propertyContext *> section_property();
    Section_propertyContext* section_property(size_t i);
    std::vector<Section_composite_structureContext *> section_composite_structure();
    Section_composite_structureContext* section_composite_structure(size_t i);

   
  };

  Def_packageContext* def_package();

  class  Def_systemContext : public antlr4::ParserRuleContext {
  public:
    sep::System * sys;
    FMLParser::Executable_modifier_specifierContext *ms = nullptr;
    antlr4::Token *id = nullptr;
    antlr4::Token *stringliteralToken = nullptr;
    Def_systemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LCURLY();
    antlr4::tree::TerminalNode *RCURLY();
    antlr4::tree::TerminalNode *ID();
    antlr4::tree::TerminalNode *LT_();
    Executable_specifierContext *executable_specifier();
    antlr4::tree::TerminalNode *GT();
    antlr4::tree::TerminalNode *StringLiteral();
    Section_headerContext *section_header();
    Section_importContext *section_import();
    std::vector<Section_parameterContext *> section_parameter();
    Section_parameterContext* section_parameter(size_t i);
    std::vector<Section_propertyContext *> section_property();
    Section_propertyContext* section_property(size_t i);
    std::vector<Section_composite_structureContext *> section_composite_structure();
    Section_composite_structureContext* section_composite_structure(size_t i);
    Section_behaviorContext *section_behavior();
    Section_statemachineContext *section_statemachine();
    std::vector<Section_model_of_computationContext *> section_model_of_computation();
    Section_model_of_computationContext* section_model_of_computation(size_t i);
    std::vector<Section_model_of_interactionContext *> section_model_of_interaction();
    Section_model_of_interactionContext* section_model_of_interaction(size_t i);
    std::vector<Section_model_of_executionContext *> section_model_of_execution();
    Section_model_of_executionContext* section_model_of_execution(size_t i);
    Executable_modifier_specifierContext *executable_modifier_specifier();

   
  };

  Def_systemContext* def_system();

  class  QualifiedNameIDContext : public antlr4::ParserRuleContext {
  public:
    std::string s;
    std::size_t nb = 1;
    antlr4::Token *id = nullptr;
    QualifiedNameIDContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<antlr4::tree::TerminalNode *> ID();
    antlr4::tree::TerminalNode* ID(size_t i);
    std::vector<antlr4::tree::TerminalNode *> DOT();
    antlr4::tree::TerminalNode* DOT(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COLONx2();
    antlr4::tree::TerminalNode* COLONx2(size_t i);

   
  };

  QualifiedNameIDContext* qualifiedNameID();

  class  Integer_constantContext : public antlr4::ParserRuleContext {
  public:
    std::size_t val;
    antlr4::Token *n = nullptr;
    FMLParser::QualifiedNameIDContext *cid = nullptr;
    Integer_constantContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *IntegerLiteral();
    QualifiedNameIDContext *qualifiedNameID();

   
  };

  Integer_constantContext* integer_constant();

  class  Float_constantContext : public antlr4::ParserRuleContext {
  public:
    sep::avm_float_t val;
    antlr4::Token *f = nullptr;
    FMLParser::QualifiedNameIDContext *cid = nullptr;
    Float_constantContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *FloatLiteral();
    QualifiedNameIDContext *qualifiedNameID();

   
  };

  Float_constantContext* float_constant();

  class  Section_headerContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * container;
    Section_headerContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Section_headerContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * container);
    virtual size_t getRuleIndex() const override;

   
  };

  Section_headerContext* section_header(sep::Machine * container);

  class  Section_importContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * container;
    Section_importContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Section_importContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * container);
    virtual size_t getRuleIndex() const override;
    std::vector<Include_packageContext *> include_package();
    Include_packageContext* include_package(size_t i);

   
  };

  Section_importContext* section_import(sep::Machine * container);

  class  Include_packageContext : public antlr4::ParserRuleContext {
  public:
    Include_packageContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<antlr4::tree::TerminalNode *> StringLiteral();
    antlr4::tree::TerminalNode* StringLiteral(size_t i);
    antlr4::tree::TerminalNode *SEMI();
    antlr4::tree::TerminalNode *LCURLY();
    antlr4::tree::TerminalNode *RCURLY();

   
  };

  Include_packageContext* include_package();

  class  Section_procedureContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * container;
    FMLParser::Def_procedureContext *p = nullptr;
    Section_procedureContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Section_procedureContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * container);
    virtual size_t getRuleIndex() const override;
    std::vector<Def_procedureContext *> def_procedure();
    Def_procedureContext* def_procedure(size_t i);

   
  };

  Section_procedureContext* section_procedure(sep::Machine * container);

  class  Def_procedureContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * container;
    sep::Machine * procedure;
    FMLParser::Procedure_modifier_specifierContext *ms = nullptr;
    antlr4::Token *id = nullptr;
    antlr4::Token *stringliteralToken = nullptr;
    Def_procedureContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_procedureContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * container);
    virtual size_t getRuleIndex() const override;
    Def_body_procedureContext *def_body_procedure();
    antlr4::tree::TerminalNode *ID();
    antlr4::tree::TerminalNode *LT_();
    Executable_specifierContext *executable_specifier();
    antlr4::tree::TerminalNode *GT();
    antlr4::tree::TerminalNode *StringLiteral();
    Def_machine_parametersContext *def_machine_parameters();
    Def_machine_returnsContext *def_machine_returns();
    Procedure_modifier_specifierContext *procedure_modifier_specifier();

   
  };

  Def_procedureContext* def_procedure(sep::Machine * container);

  class  Def_machine_parametersContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * machine;
    Def_machine_parametersContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_machine_parametersContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * machine);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LBRACKET();
    std::vector<Def_machine_variable_parameter_atomContext *> def_machine_variable_parameter_atom();
    Def_machine_variable_parameter_atomContext* def_machine_variable_parameter_atom(size_t i);
    antlr4::tree::TerminalNode *RBRACKET();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    antlr4::tree::TerminalNode *LPAREN();
    antlr4::tree::TerminalNode *RPAREN();

   
  };

  Def_machine_parametersContext* def_machine_parameters(sep::Machine * machine);

  class  Def_machine_variable_parameter_atomContext : public antlr4::ParserRuleContext {
  public:
    sep::PropertyPart * paramDecl;
    sep::Modifier mdfr;
    sep::avm_offset_t offset;
    FMLParser::Modifier_paramContext *m = nullptr;
    FMLParser::Type_varContext *tv = nullptr;
    antlr4::Token *id = nullptr;
    FMLParser::Initial_valueContext *iv = nullptr;
    FMLParser::ExpressionContext *e = nullptr;
    FMLParser::QualifiedNameIDContext *vid = nullptr;
    Def_machine_variable_parameter_atomContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_machine_variable_parameter_atomContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::PropertyPart * paramDecl, sep::Modifier mdfr, sep::avm_offset_t offset);
    virtual size_t getRuleIndex() const override;
    Type_varContext *type_var();
    Modifier_paramContext *modifier_param();
    antlr4::tree::TerminalNode *ID();
    Initial_valueContext *initial_value();
    antlr4::tree::TerminalNode *COLON();
    ExpressionContext *expression();
    QualifiedNameIDContext *qualifiedNameID();

   
  };

  Def_machine_variable_parameter_atomContext* def_machine_variable_parameter_atom(sep::PropertyPart * paramDecl,sep::Modifier mdfr,sep::avm_offset_t offset);

  class  Def_machine_returnsContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * machine;
    sep::Modifier mdfr;
    FMLParser::Type_varContext *tv = nullptr;
    FMLParser::Initial_valueContext *iv = nullptr;
    Def_machine_returnsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_machine_returnsContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * machine, sep::Modifier mdfr);
    virtual size_t getRuleIndex() const override;
    Type_varContext *type_var();
    antlr4::tree::TerminalNode *LBRACKET();
    std::vector<Def_machine_variable_return_atomContext *> def_machine_variable_return_atom();
    Def_machine_variable_return_atomContext* def_machine_variable_return_atom(size_t i);
    antlr4::tree::TerminalNode *RBRACKET();
    antlr4::tree::TerminalNode *LPAREN();
    antlr4::tree::TerminalNode *RPAREN();
    Initial_valueContext *initial_value();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

   
  };

  Def_machine_returnsContext* def_machine_returns(sep::Machine * machine,sep::Modifier mdfr);

  class  Def_machine_variable_return_atomContext : public antlr4::ParserRuleContext {
  public:
    sep::PropertyPart * paramDecl;
    sep::Modifier mdfr;
    sep::avm_offset_t offset;
    FMLParser::Modifier_paramContext *m = nullptr;
    FMLParser::Type_varContext *tv = nullptr;
    antlr4::Token *id = nullptr;
    FMLParser::Initial_valueContext *iv = nullptr;
    FMLParser::ExpressionContext *e = nullptr;
    FMLParser::QualifiedNameIDContext *vid = nullptr;
    Def_machine_variable_return_atomContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_machine_variable_return_atomContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::PropertyPart * paramDecl, sep::Modifier mdfr, sep::avm_offset_t offset);
    virtual size_t getRuleIndex() const override;
    Type_varContext *type_var();
    Modifier_paramContext *modifier_param();
    antlr4::tree::TerminalNode *ID();
    Initial_valueContext *initial_value();
    antlr4::tree::TerminalNode *COLON();
    ExpressionContext *expression();
    QualifiedNameIDContext *qualifiedNameID();

   
  };

  Def_machine_variable_return_atomContext* def_machine_variable_return_atom(sep::PropertyPart * paramDecl,sep::Modifier mdfr,sep::avm_offset_t offset);

  class  Def_body_procedureContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * procedure;
    Def_body_procedureContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_body_procedureContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * procedure);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LCURLY();
    antlr4::tree::TerminalNode *RCURLY();
    Def_body_procedure_sectionContext *def_body_procedure_section();
    Def_body_procedure_simplifContext *def_body_procedure_simplif();

   
  };

  Def_body_procedureContext* def_body_procedure(sep::Machine * procedure);

  class  Def_body_procedure_sectionContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * procedure;
    Def_body_procedure_sectionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_body_procedure_sectionContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * procedure);
    virtual size_t getRuleIndex() const override;
    Section_headerContext *section_header();
    Section_importContext *section_import();
    std::vector<Section_parameterContext *> section_parameter();
    Section_parameterContext* section_parameter(size_t i);
    std::vector<Section_propertyContext *> section_property();
    Section_propertyContext* section_property(size_t i);
    std::vector<Section_composite_structureContext *> section_composite_structure();
    Section_composite_structureContext* section_composite_structure(size_t i);
    Section_behaviorContext *section_behavior();
    Section_statemachineContext *section_statemachine();
    std::vector<Section_model_of_computationContext *> section_model_of_computation();
    Section_model_of_computationContext* section_model_of_computation(size_t i);
    std::vector<Section_model_of_executionContext *> section_model_of_execution();
    Section_model_of_executionContext* section_model_of_execution(size_t i);
    std::vector<Section_model_of_interactionContext *> section_model_of_interaction();
    Section_model_of_interactionContext* section_model_of_interaction(size_t i);

   
  };

  Def_body_procedure_sectionContext* def_body_procedure_section(sep::Machine * procedure);

  class  Def_body_procedure_simplifContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * procedure;
    FMLParser::Modifier_declarationContext *m = nullptr;
    FMLParser::Any_def_statemachineContext *ads = nullptr;
    Def_body_procedure_simplifContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_body_procedure_simplifContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * procedure);
    virtual size_t getRuleIndex() const override;
    std::vector<Decl_variableContext *> decl_variable();
    Decl_variableContext* decl_variable(size_t i);
    std::vector<Def_state_activityContext *> def_state_activity();
    Def_state_activityContext* def_state_activity(size_t i);
    std::vector<Any_def_statemachineContext *> any_def_statemachine();
    Any_def_statemachineContext* any_def_statemachine(size_t i);
    std::vector<Modifier_declarationContext *> modifier_declaration();
    Modifier_declarationContext* modifier_declaration(size_t i);

   
  };

  Def_body_procedure_simplifContext* def_body_procedure_simplif(sep::Machine * procedure);

  class  Section_composite_structureContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * container;
    Section_composite_structureContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Section_composite_structureContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * container);
    virtual size_t getRuleIndex() const override;
    Section_routineContext *section_routine();
    Section_procedureContext *section_procedure();
    Section_composite_genericContext *section_composite_generic();
    Section_machine_modelContext *section_machine_model();
    Section_machine_prototypeContext *section_machine_prototype();
    Section_machine_instanceContext *section_machine_instance();

   
  };

  Section_composite_structureContext* section_composite_structure(sep::Machine * container);

  class  Section_composite_genericContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * container;
    FMLParser::Executable_machineContext *m = nullptr;
    Section_composite_genericContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Section_composite_genericContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * container);
    virtual size_t getRuleIndex() const override;
    std::vector<Executable_machineContext *> executable_machine();
    Executable_machineContext* executable_machine(size_t i);

   
  };

  Section_composite_genericContext* section_composite_generic(sep::Machine * container);

  class  Section_machine_modelContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * container;
    FMLParser::Executable_model_definitonContext *m = nullptr;
    Section_machine_modelContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Section_machine_modelContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * container);
    virtual size_t getRuleIndex() const override;
    std::vector<Executable_model_definitonContext *> executable_model_definiton();
    Executable_model_definitonContext* executable_model_definiton(size_t i);

   
  };

  Section_machine_modelContext* section_machine_model(sep::Machine * container);

  class  Section_machine_prototypeContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * container;
    FMLParser::Executable_model_definitonContext *m = nullptr;
    Section_machine_prototypeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Section_machine_prototypeContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * container);
    virtual size_t getRuleIndex() const override;
    std::vector<Executable_model_definitonContext *> executable_model_definiton();
    Executable_model_definitonContext* executable_model_definiton(size_t i);

   
  };

  Section_machine_prototypeContext* section_machine_prototype(sep::Machine * container);

  class  Section_machine_instanceContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * container;
    FMLParser::Executable_instance_definitonContext *edi = nullptr;
    Section_machine_instanceContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Section_machine_instanceContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * container);
    virtual size_t getRuleIndex() const override;
    std::vector<Executable_instance_definitonContext *> executable_instance_definiton();
    Executable_instance_definitonContext* executable_instance_definiton(size_t i);

   
  };

  Section_machine_instanceContext* section_machine_instance(sep::Machine * container);

  class  Executable_machineContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * container;
    sep::Machine * machine;
    FMLParser::Executable_modifier_specifierContext *ms = nullptr;
    FMLParser::Def_machineContext *dm = nullptr;
    FMLParser::Any_def_statemachineContext *ads = nullptr;
    FMLParser::Decl_instanceContext *emi = nullptr;
    Executable_machineContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Executable_machineContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * container);
    virtual size_t getRuleIndex() const override;
    Def_machineContext *def_machine();
    Any_def_statemachineContext *any_def_statemachine();
    Decl_instanceContext *decl_instance();
    Executable_modifier_specifierContext *executable_modifier_specifier();

   
  };

  Executable_machineContext* executable_machine(sep::Machine * container);

  class  Executable_model_definitonContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * container;
    sep::Modifier mdfr;
    sep::Specifier spcfr;
    sep::Machine * machine;
    FMLParser::Executable_modifier_specifierContext *ms = nullptr;
    FMLParser::Def_machineContext *dm = nullptr;
    FMLParser::Def_statemachineContext *ads = nullptr;
    Executable_model_definitonContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Executable_model_definitonContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * container, sep::Modifier mdfr, sep::Specifier spcfr);
    virtual size_t getRuleIndex() const override;
    Def_machineContext *def_machine();
    Def_statemachineContext *def_statemachine();
    Executable_modifier_specifierContext *executable_modifier_specifier();

   
  };

  Executable_model_definitonContext* executable_model_definiton(sep::Machine * container,sep::Modifier mdfr,sep::Specifier spcfr);

  class  Executable_instance_definitonContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * container;
    sep::Machine * instance;
    FMLParser::Instance_modifier_specifierContext *ms = nullptr;
    FMLParser::Decl_instanceContext *emi = nullptr;
    Executable_instance_definitonContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Executable_instance_definitonContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * container);
    virtual size_t getRuleIndex() const override;
    Decl_instanceContext *decl_instance();
    Instance_modifier_specifierContext *instance_modifier_specifier();

   
  };

  Executable_instance_definitonContext* executable_instance_definiton(sep::Machine * container);

  class  Decl_instanceContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * container;
    sep::Modifier mdfr;
    sep::Specifier spcfr;
    sep::Machine * instance;
    FMLParser::Instance_machine_modelContext *mm = nullptr;
    antlr4::Token *id = nullptr;
    antlr4::Token *stringliteralToken = nullptr;
    FMLParser::StatementContext *s = nullptr;
    Decl_instanceContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Decl_instanceContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * container, sep::Modifier mdfr, sep::Specifier spcfr);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LT_();
    antlr4::tree::TerminalNode *GT();
    Instance_machine_modelContext *instance_machine_model();
    antlr4::tree::TerminalNode *ID();
    antlr4::tree::TerminalNode *SEMI();
    antlr4::tree::TerminalNode *LCURLY();
    antlr4::tree::TerminalNode *RCURLY();
    antlr4::tree::TerminalNode *COMMA();
    Def_instance_countContext *def_instance_count();
    antlr4::tree::TerminalNode *StringLiteral();
    antlr4::tree::TerminalNode *LPAREN();
    antlr4::tree::TerminalNode *RPAREN();
    std::vector<Def_instance_activityContext *> def_instance_activity();
    Def_instance_activityContext* def_instance_activity(size_t i);
    Def_instance_on_new_activityContext *def_instance_on_new_activity();
    std::vector<StatementContext *> statement();
    StatementContext* statement(size_t i);

   
  };

  Decl_instanceContext* decl_instance(sep::Machine * container,sep::Modifier mdfr,sep::Specifier spcfr);

  class  Def_instance_on_new_activityContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * instance;
    Def_instance_on_new_activityContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_instance_on_new_activityContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * instance);
    virtual size_t getRuleIndex() const override;
    std::vector<Def_instance_on_new_activity_parameterContext *> def_instance_on_new_activity_parameter();
    Def_instance_on_new_activity_parameterContext* def_instance_on_new_activity_parameter(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

   
  };

  Def_instance_on_new_activityContext* def_instance_on_new_activity(sep::Machine * instance);

  class  Def_instance_on_new_activity_parameterContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * instance;
    std::size_t position;
    FMLParser::LvalueContext *lv = nullptr;
    FMLParser::Op_assign_paramContext *oap = nullptr;
    FMLParser::ExpressionContext *e = nullptr;
    Def_instance_on_new_activity_parameterContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_instance_on_new_activity_parameterContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * instance, std::size_t position);
    virtual size_t getRuleIndex() const override;
    LvalueContext *lvalue();
    Op_assign_paramContext *op_assign_param();
    ExpressionContext *expression();

   
  };

  Def_instance_on_new_activity_parameterContext* def_instance_on_new_activity_parameter(sep::Machine * instance,std::size_t position);

  class  Op_assign_paramContext : public antlr4::ParserRuleContext {
  public:
    const sep::Operator * op;
    Op_assign_paramContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ASSIGN();
    antlr4::tree::TerminalNode *COLON();
    antlr4::tree::TerminalNode *ASSIGN_REF();
    antlr4::tree::TerminalNode *ASSIGN_MACRO();

   
  };

  Op_assign_paramContext* op_assign_param();

  class  Def_instance_activityContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * instance;
    FMLParser::Block_statementContext *bs = nullptr;
    Def_instance_activityContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_instance_activityContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * instance);
    virtual size_t getRuleIndex() const override;
    Block_statementContext *block_statement();

   
  };

  Def_instance_activityContext* def_instance_activity(sep::Machine * instance);

  class  Section_behaviorContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * container;
    FMLParser::Executable_machineContext *m = nullptr;
    Section_behaviorContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Section_behaviorContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * container);
    virtual size_t getRuleIndex() const override;
    std::vector<Executable_machineContext *> executable_machine();
    Executable_machineContext* executable_machine(size_t i);

   
  };

  Section_behaviorContext* section_behavior(sep::Machine * container);

  class  Def_instance_countContext : public antlr4::ParserRuleContext {
  public:
    std::size_t * initial;
    std::size_t * maximal;
    FMLParser::Integer_constantContext *n = nullptr;
    Def_instance_countContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_instance_countContext(antlr4::ParserRuleContext *parent, size_t invokingState, std::size_t * initial, std::size_t * maximal);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LBRACKET();
    antlr4::tree::TerminalNode *RBRACKET();
    antlr4::tree::TerminalNode *LPAREN();
    std::vector<Def_instance_count_atomContext *> def_instance_count_atom();
    Def_instance_count_atomContext* def_instance_count_atom(size_t i);
    antlr4::tree::TerminalNode *RPAREN();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    antlr4::tree::TerminalNode *STAR();
    antlr4::tree::TerminalNode *PLUS();
    std::vector<Integer_constantContext *> integer_constant();
    Integer_constantContext* integer_constant(size_t i);

   
  };

  Def_instance_countContext* def_instance_count(std::size_t * initial,std::size_t * maximal);

  class  Def_instance_count_atomContext : public antlr4::ParserRuleContext {
  public:
    std::size_t * initial;
    std::size_t * maximal;
    FMLParser::Integer_constantContext *n = nullptr;
    Def_instance_count_atomContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_instance_count_atomContext(antlr4::ParserRuleContext *parent, size_t invokingState, std::size_t * initial, std::size_t * maximal);
    virtual size_t getRuleIndex() const override;
    Integer_constantContext *integer_constant();

   
  };

  Def_instance_count_atomContext* def_instance_count_atom(std::size_t * initial,std::size_t * maximal);

  class  Def_machineContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * container;
    sep::Modifier mdfr;
    sep::Specifier spcfr;
    sep::Machine * machine;
    antlr4::Token *id = nullptr;
    antlr4::Token *stringliteralToken = nullptr;
    Def_machineContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_machineContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * container, sep::Modifier mdfr, sep::Specifier spcfr);
    virtual size_t getRuleIndex() const override;
    Def_body_machineContext *def_body_machine();
    antlr4::tree::TerminalNode *ID();
    antlr4::tree::TerminalNode *LT_();
    antlr4::tree::TerminalNode *GT();
    antlr4::tree::TerminalNode *StringLiteral();
    Def_machine_parametersContext *def_machine_parameters();
    Def_machine_returnsContext *def_machine_returns();
    Executable_specifierContext *executable_specifier();
    Def_instance_countContext *def_instance_count();
    antlr4::tree::TerminalNode *COMMA();

   
  };

  Def_machineContext* def_machine(sep::Machine * container,sep::Modifier mdfr,sep::Specifier spcfr);

  class  Def_body_machineContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * machine;
    Def_body_machineContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_body_machineContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * machine);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LCURLY();
    Def_body_machine_sectionContext *def_body_machine_section();
    antlr4::tree::TerminalNode *RCURLY();

   
  };

  Def_body_machineContext* def_body_machine(sep::Machine * machine);

  class  Def_body_machine_sectionContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * machine;
    Def_body_machine_sectionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_body_machine_sectionContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * machine);
    virtual size_t getRuleIndex() const override;
    Section_headerContext *section_header();
    Section_importContext *section_import();
    std::vector<Section_parameterContext *> section_parameter();
    Section_parameterContext* section_parameter(size_t i);
    std::vector<Section_propertyContext *> section_property();
    Section_propertyContext* section_property(size_t i);
    std::vector<Section_composite_structureContext *> section_composite_structure();
    Section_composite_structureContext* section_composite_structure(size_t i);
    Section_behaviorContext *section_behavior();
    Section_statemachineContext *section_statemachine();
    std::vector<Section_model_of_computationContext *> section_model_of_computation();
    Section_model_of_computationContext* section_model_of_computation(size_t i);
    std::vector<Section_model_of_executionContext *> section_model_of_execution();
    Section_model_of_executionContext* section_model_of_execution(size_t i);
    std::vector<Section_model_of_interactionContext *> section_model_of_interaction();
    Section_model_of_interactionContext* section_model_of_interaction(size_t i);

   
  };

  Def_body_machine_sectionContext* def_body_machine_section(sep::Machine * machine);

  class  Def_body_machine_simplifContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * machine;
    Def_body_machine_simplifContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_body_machine_simplifContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * machine);
    virtual size_t getRuleIndex() const override;
    std::vector<Property_declarationContext *> property_declaration();
    Property_declarationContext* property_declaration(size_t i);
    std::vector<Def_moe_primitiveContext *> def_moe_primitive();
    Def_moe_primitiveContext* def_moe_primitive(size_t i);

   
  };

  Def_body_machine_simplifContext* def_body_machine_simplif(sep::Machine * machine);

  class  Any_def_statemachineContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * container;
    sep::Modifier mdfr;
    sep::Specifier spcfr;
    sep::Machine * machine;
    FMLParser::Executable_modifier_specifierContext *ms = nullptr;
    FMLParser::Def_state_singletonContext *dss = nullptr;
    FMLParser::Def_stateContext *ds = nullptr;
    FMLParser::Def_statemachineContext *sm = nullptr;
    Any_def_statemachineContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Any_def_statemachineContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * container, sep::Modifier mdfr, sep::Specifier spcfr);
    virtual size_t getRuleIndex() const override;
    Def_state_singletonContext *def_state_singleton();
    Def_stateContext *def_state();
    Def_statemachineContext *def_statemachine();
    Executable_modifier_specifierContext *executable_modifier_specifier();

   
  };

  Any_def_statemachineContext* any_def_statemachine(sep::Machine * container,sep::Modifier mdfr,sep::Specifier spcfr);

  class  Def_statemachineContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * container;
    sep::Modifier mdfr;
    sep::Specifier spcfr;
    sep::Machine * machine;
    antlr4::Token *id = nullptr;
    antlr4::Token *stringliteralToken = nullptr;
    Def_statemachineContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_statemachineContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * container, sep::Modifier mdfr, sep::Specifier spcfr);
    virtual size_t getRuleIndex() const override;
    Def_body_statemachineContext *def_body_statemachine();
    antlr4::tree::TerminalNode *RBRACKET();
    antlr4::tree::TerminalNode *LT_();
    antlr4::tree::TerminalNode *GT();
    std::vector<antlr4::tree::TerminalNode *> ID();
    antlr4::tree::TerminalNode* ID(size_t i);
    antlr4::tree::TerminalNode *StringLiteral();
    Def_machine_parametersContext *def_machine_parameters();
    Def_machine_returnsContext *def_machine_returns();
    antlr4::tree::TerminalNode *LBRACKET();
    antlr4::tree::TerminalNode *LBRACKET_EXCEPT();
    antlr4::tree::TerminalNode *STAR();
    Executable_specifierContext *executable_specifier();
    Def_instance_countContext *def_instance_count();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

   
  };

  Def_statemachineContext* def_statemachine(sep::Machine * container,sep::Modifier mdfr,sep::Specifier spcfr);

  class  Def_body_statemachineContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * machine;
    Def_body_statemachineContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_body_statemachineContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * machine);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LCURLY();
    antlr4::tree::TerminalNode *RCURLY();
    Section_headerContext *section_header();
    Section_importContext *section_import();
    std::vector<Section_parameterContext *> section_parameter();
    Section_parameterContext* section_parameter(size_t i);
    std::vector<Section_propertyContext *> section_property();
    Section_propertyContext* section_property(size_t i);
    std::vector<Section_composite_structureContext *> section_composite_structure();
    Section_composite_structureContext* section_composite_structure(size_t i);
    Section_state_regionContext *section_state_region();
    Section_transitionContext *section_transition();
    std::vector<Section_model_of_computationContext *> section_model_of_computation();
    Section_model_of_computationContext* section_model_of_computation(size_t i);
    std::vector<Section_model_of_executionContext *> section_model_of_execution();
    Section_model_of_executionContext* section_model_of_execution(size_t i);
    std::vector<Section_model_of_interactionContext *> section_model_of_interaction();
    Section_model_of_interactionContext* section_model_of_interaction(size_t i);
    std::vector<Section_composite_regionContext *> section_composite_region();
    Section_composite_regionContext* section_composite_region(size_t i);

   
  };

  Def_body_statemachineContext* def_body_statemachine(sep::Machine * machine);

  class  Section_state_regionContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * container;
    FMLParser::Any_def_statemachineContext *m = nullptr;
    Section_state_regionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Section_state_regionContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * container);
    virtual size_t getRuleIndex() const override;
    std::vector<Any_def_statemachineContext *> any_def_statemachine();
    Any_def_statemachineContext* any_def_statemachine(size_t i);

   
  };

  Section_state_regionContext* section_state_region(sep::Machine * container);

  class  Section_composite_regionContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * container;
    antlr4::Token *id = nullptr;
    antlr4::Token *sl = nullptr;
    FMLParser::Any_def_statemachineContext *m = nullptr;
    Section_composite_regionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Section_composite_regionContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * container);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ID();
    antlr4::tree::TerminalNode *StringLiteral();
    std::vector<Any_def_statemachineContext *> any_def_statemachine();
    Any_def_statemachineContext* any_def_statemachine(size_t i);

   
  };

  Section_composite_regionContext* section_composite_region(sep::Machine * container);

  class  Section_statemachineContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * container;
    FMLParser::Any_def_statemachineContext *m = nullptr;
    Section_statemachineContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Section_statemachineContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * container);
    virtual size_t getRuleIndex() const override;
    std::vector<Any_def_statemachineContext *> any_def_statemachine();
    Any_def_statemachineContext* any_def_statemachine(size_t i);

   
  };

  Section_statemachineContext* section_statemachine(sep::Machine * container);

  class  Def_stateContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * container;
    sep::Modifier mdfr;
    sep::Specifier spcfr;
    sep::Machine * state = nullptr;
    FMLParser::State_idContext *id = nullptr;
    antlr4::Token *stringliteralToken = nullptr;
    Def_stateContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_stateContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * container, sep::Modifier mdfr, sep::Specifier spcfr);
    virtual size_t getRuleIndex() const override;
    Def_body_stateContext *def_body_state();
    antlr4::tree::TerminalNode *SEMI();
    antlr4::tree::TerminalNode *LT_();
    Executable_specifierContext *executable_specifier();
    antlr4::tree::TerminalNode *GT();
    antlr4::tree::TerminalNode *RBRACKET();
    antlr4::tree::TerminalNode *StringLiteral();
    std::vector<State_idContext *> state_id();
    State_idContext* state_id(size_t i);
    antlr4::tree::TerminalNode *LBRACKET();
    antlr4::tree::TerminalNode *LBRACKET_EXCEPT();
    antlr4::tree::TerminalNode *STAR();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

   
  };

  Def_stateContext* def_state(sep::Machine * container,sep::Modifier mdfr,sep::Specifier spcfr);

  class  State_kw_idContext : public antlr4::ParserRuleContext {
  public:
    std::string s;
    State_kw_idContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;

   
  };

  State_kw_idContext* state_kw_id();

  class  State_idContext : public antlr4::ParserRuleContext {
  public:
    std::string s;
    FMLParser::State_kw_idContext *kw = nullptr;
    antlr4::Token *id = nullptr;
    State_idContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    State_kw_idContext *state_kw_id();
    antlr4::tree::TerminalNode *ID();
    antlr4::tree::TerminalNode *DOLLAR();

   
  };

  State_idContext* state_id();

  class  Def_state_singletonContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * container;
    sep::Modifier mdfr;
    sep::Specifier spcfr;
    sep::Machine * state;
    FMLParser::Block_statementContext *bs = nullptr;
    Def_state_singletonContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_state_singletonContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * container, sep::Modifier mdfr, sep::Specifier spcfr);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LCURLY();
    Def_body_state_simplifContext *def_body_state_simplif();
    antlr4::tree::TerminalNode *RCURLY();
    Block_statementContext *block_statement();

   
  };

  Def_state_singletonContext* def_state_singleton(sep::Machine * container,sep::Modifier mdfr,sep::Specifier spcfr);

  class  Executable_specifierContext : public antlr4::ParserRuleContext {
  public:
    sep::Specifier * spcfr;
    FMLParser::Executable_specifier_atomContext *ka = nullptr;
    Executable_specifierContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Executable_specifierContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Specifier * spcfr);
    virtual size_t getRuleIndex() const override;
    std::vector<Executable_specifier_atomContext *> executable_specifier_atom();
    Executable_specifier_atomContext* executable_specifier_atom(size_t i);
    std::vector<antlr4::tree::TerminalNode *> BAND();
    antlr4::tree::TerminalNode* BAND(size_t i);

   
  };

  Executable_specifierContext* executable_specifier(sep::Specifier * spcfr);

  class  Executable_specifier_atomContext : public antlr4::ParserRuleContext {
  public:
    sep::Specifier * spcfr;
    antlr4::Token *id = nullptr;
    Executable_specifier_atomContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Executable_specifier_atomContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Specifier * spcfr);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ID();

   
  };

  Executable_specifier_atomContext* executable_specifier_atom(sep::Specifier * spcfr);

  class  Instance_machine_modelContext : public antlr4::ParserRuleContext {
  public:
    sep::BF model;
    FMLParser::QualifiedNameIDContext *tid = nullptr;
    Instance_machine_modelContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    QualifiedNameIDContext *qualifiedNameID();

   
  };

  Instance_machine_modelContext* instance_machine_model();

  class  Def_body_stateContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * state;
    Def_body_stateContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_body_stateContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * state);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LCURLY();
    antlr4::tree::TerminalNode *RCURLY();
    Def_body_state_sectionContext *def_body_state_section();
    Def_body_state_simplifContext *def_body_state_simplif();

   
  };

  Def_body_stateContext* def_body_state(sep::Machine * state);

  class  Def_body_state_sectionContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * machine;
    Def_body_state_sectionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_body_state_sectionContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * machine);
    virtual size_t getRuleIndex() const override;
    std::vector<Section_propertyContext *> section_property();
    Section_propertyContext* section_property(size_t i);
    std::vector<Section_composite_structureContext *> section_composite_structure();
    Section_composite_structureContext* section_composite_structure(size_t i);
    Section_state_regionContext *section_state_region();
    Section_transitionContext *section_transition();
    std::vector<Section_model_of_computationContext *> section_model_of_computation();
    Section_model_of_computationContext* section_model_of_computation(size_t i);
    std::vector<Section_model_of_executionContext *> section_model_of_execution();
    Section_model_of_executionContext* section_model_of_execution(size_t i);
    std::vector<Section_model_of_interactionContext *> section_model_of_interaction();
    Section_model_of_interactionContext* section_model_of_interaction(size_t i);
    std::vector<Section_composite_regionContext *> section_composite_region();
    Section_composite_regionContext* section_composite_region(size_t i);

   
  };

  Def_body_state_sectionContext* def_body_state_section(sep::Machine * machine);

  class  Def_body_state_simplifContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * state;
    FMLParser::Modifier_declarationContext *m = nullptr;
    FMLParser::Any_def_statemachineContext *ads = nullptr;
    Def_body_state_simplifContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_body_state_simplifContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * state);
    virtual size_t getRuleIndex() const override;
    std::vector<Decl_variableContext *> decl_variable();
    Decl_variableContext* decl_variable(size_t i);
    std::vector<Def_transitionContext *> def_transition();
    Def_transitionContext* def_transition(size_t i);
    std::vector<Def_state_activityContext *> def_state_activity();
    Def_state_activityContext* def_state_activity(size_t i);
    std::vector<Any_def_statemachineContext *> any_def_statemachine();
    Any_def_statemachineContext* any_def_statemachine(size_t i);
    std::vector<Modifier_declarationContext *> modifier_declaration();
    Modifier_declarationContext* modifier_declaration(size_t i);

   
  };

  Def_body_state_simplifContext* def_body_state_simplif(sep::Machine * state);

  class  Section_transitionContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * state;
    FMLParser::Modifier_transitionContext *m = nullptr;
    Section_transitionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Section_transitionContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * state);
    virtual size_t getRuleIndex() const override;
    std::vector<Def_transitionContext *> def_transition();
    Def_transitionContext* def_transition(size_t i);
    std::vector<Modifier_transitionContext *> modifier_transition();
    Modifier_transitionContext* modifier_transition(size_t i);

   
  };

  Section_transitionContext* section_transition(sep::Machine * state);

  class  Def_transitionContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * state;
    sep::Modifier mdfr;
    sep::Specifier spcfr;
    antlr4::Token *tok = nullptr;
    antlr4::Token *id = nullptr;
    antlr4::Token *stringliteralToken = nullptr;
    Def_transitionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_transitionContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * state, sep::Modifier mdfr, sep::Specifier spcfr);
    virtual size_t getRuleIndex() const override;
    Moe_transitionContext *moe_transition();
    antlr4::tree::TerminalNode *LT_();
    Moc_transitionContext *moc_transition();
    antlr4::tree::TerminalNode *GT();
    antlr4::tree::TerminalNode *AT_ID();
    antlr4::tree::TerminalNode *StringLiteral();
    antlr4::tree::TerminalNode *ID();

   
  };

  Def_transitionContext* def_transition(sep::Machine * state,sep::Modifier mdfr,sep::Specifier spcfr);

  class  Kind_transitionContext : public antlr4::ParserRuleContext {
  public:
    sep::Transition::MOC_KIND kind;
    antlr4::Token *id = nullptr;
    Kind_transitionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ID();

   
  };

  Kind_transitionContext* kind_transition();

  class  Moc_transition_attributeContext : public antlr4::ParserRuleContext {
  public:
    sep::Transition::moc_kind_t kind;
    FMLParser::Kind_transitionContext *kt = nullptr;
    Moc_transition_attributeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Kind_transitionContext *kind_transition();
    antlr4::tree::TerminalNode *BAND();

   
  };

  Moc_transition_attributeContext* moc_transition_attribute();

  class  Moc_transitionContext : public antlr4::ParserRuleContext {
  public:
    sep::Transition * trans;
    Moc_transitionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Moc_transitionContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Transition * trans);
    virtual size_t getRuleIndex() const override;
    std::vector<Moc_transition_atomContext *> moc_transition_atom();
    Moc_transition_atomContext* moc_transition_atom(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

   
  };

  Moc_transitionContext* moc_transition(sep::Transition * trans);

  class  Moc_transition_atomContext : public antlr4::ParserRuleContext {
  public:
    sep::Transition * trans;
    FMLParser::Moc_transition_attributeContext *kt = nullptr;
    FMLParser::Integer_constantContext *n = nullptr;
    FMLParser::Float_constantContext *p = nullptr;
    Moc_transition_atomContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Moc_transition_atomContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Transition * trans);
    virtual size_t getRuleIndex() const override;
    Moc_transition_attributeContext *moc_transition_attribute();
    Integer_constantContext *integer_constant();
    Float_constantContext *float_constant();

   
  };

  Moc_transition_atomContext* moc_transition_atom(sep::Transition * trans);

  class  Moe_transitionContext : public antlr4::ParserRuleContext {
  public:
    sep::Transition * trans;
    FMLParser::Transition_statementContext *bs = nullptr;
    FMLParser::Target_state_idContext *tid = nullptr;
    Moe_transitionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Moe_transitionContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Transition * trans);
    virtual size_t getRuleIndex() const override;
    Transition_statementContext *transition_statement();
    antlr4::tree::TerminalNode *SEMI();
    Target_state_idContext *target_state_id();

   
  };

  Moe_transitionContext* moe_transition(sep::Transition * trans);

  class  Transition_statementContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    FMLParser::Op_blockContext *o = nullptr;
    FMLParser::StatementContext *s = nullptr;
    Transition_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LCURLY();
    antlr4::tree::TerminalNode *RCURLY();
    Transition_triggerContext *transition_trigger();
    Transition_guardContext *transition_guard();
    Transition_timed_guardContext *transition_timed_guard();
    Transition_effectContext *transition_effect();
    Op_blockContext *op_block();
    std::vector<StatementContext *> statement();
    StatementContext* statement(size_t i);

   
  };

  Transition_statementContext* transition_statement();

  class  Transition_triggerContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    FMLParser::Statement_com_inputContext *s = nullptr;
    Transition_triggerContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Transition_triggerContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::BFCode ac);
    virtual size_t getRuleIndex() const override;
    std::vector<Statement_com_inputContext *> statement_com_input();
    Statement_com_inputContext* statement_com_input(size_t i);

   
  };

  Transition_triggerContext* transition_trigger(sep::BFCode ac);

  class  Transition_guardContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    FMLParser::Statement_guardContext *s = nullptr;
    FMLParser::ExpressionContext *e = nullptr;
    Transition_guardContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Transition_guardContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::BFCode ac);
    virtual size_t getRuleIndex() const override;
    std::vector<antlr4::tree::TerminalNode *> LBRACKET();
    antlr4::tree::TerminalNode* LBRACKET(size_t i);
    std::vector<antlr4::tree::TerminalNode *> RBRACKET();
    antlr4::tree::TerminalNode* RBRACKET(size_t i);
    std::vector<Statement_guardContext *> statement_guard();
    Statement_guardContext* statement_guard(size_t i);
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);

   
  };

  Transition_guardContext* transition_guard(sep::BFCode ac);

  class  Transition_timed_guardContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    FMLParser::Statement_timed_guardContext *s = nullptr;
    FMLParser::ExpressionContext *e = nullptr;
    Transition_timed_guardContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Transition_timed_guardContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::BFCode ac);
    virtual size_t getRuleIndex() const override;
    std::vector<antlr4::tree::TerminalNode *> LCURLY();
    antlr4::tree::TerminalNode* LCURLY(size_t i);
    std::vector<antlr4::tree::TerminalNode *> RCURLY();
    antlr4::tree::TerminalNode* RCURLY(size_t i);
    std::vector<Statement_timed_guardContext *> statement_timed_guard();
    Statement_timed_guardContext* statement_timed_guard(size_t i);
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);

   
  };

  Transition_timed_guardContext* transition_timed_guard(sep::BFCode ac);

  class  Transition_effectContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    FMLParser::StatementContext *s = nullptr;
    Transition_effectContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Transition_effectContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::BFCode ac);
    virtual size_t getRuleIndex() const override;
    std::vector<StatementContext *> statement();
    StatementContext* statement(size_t i);

   
  };

  Transition_effectContext* transition_effect(sep::BFCode ac);

  class  Target_state_idContext : public antlr4::ParserRuleContext {
  public:
    sep::BF target;
    FMLParser::Target_state_kw_idContext *kw = nullptr;
    FMLParser::QualifiedNameIDContext *u = nullptr;
    antlr4::Token *id = nullptr;
    Target_state_idContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Target_state_kw_idContext *target_state_kw_id();
    QualifiedNameIDContext *qualifiedNameID();
    antlr4::tree::TerminalNode *DOLLAR();
    antlr4::tree::TerminalNode *ID();

   
  };

  Target_state_idContext* target_state_id();

  class  Target_state_kw_idContext : public antlr4::ParserRuleContext {
  public:
    std::string s;
    Target_state_kw_idContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;

   
  };

  Target_state_kw_idContext* target_state_kw_id();

  class  Def_state_activityContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * state;
    FMLParser::Block_statementContext *bs = nullptr;
    Def_state_activityContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_state_activityContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * state);
    virtual size_t getRuleIndex() const override;
    Block_statementContext *block_statement();

   
  };

  Def_state_activityContext* def_state_activity(sep::Machine * state);

  class  Section_header_import_parameter_propertyContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * container;
    Section_header_import_parameter_propertyContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Section_header_import_parameter_propertyContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * container);
    virtual size_t getRuleIndex() const override;
    Section_headerContext *section_header();
    Section_importContext *section_import();
    Section_parameterContext *section_parameter();
    std::vector<Section_propertyContext *> section_property();
    Section_propertyContext* section_property(size_t i);
    Section_property_free_declarationContext *section_property_free_declaration();

   
  };

  Section_header_import_parameter_propertyContext* section_header_import_parameter_property(sep::Machine * container);

  class  Section_parameterContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * container;
    Section_parameterContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Section_parameterContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * container);
    virtual size_t getRuleIndex() const override;
    std::vector<Property_declarationContext *> property_declaration();
    Property_declarationContext* property_declaration(size_t i);

   
  };

  Section_parameterContext* section_parameter(sep::Machine * container);

  class  Section_propertyContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * container;
    Section_propertyContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Section_propertyContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * container);
    virtual size_t getRuleIndex() const override;
    std::vector<Property_declarationContext *> property_declaration();
    Property_declarationContext* property_declaration(size_t i);

   
  };

  Section_propertyContext* section_property(sep::Machine * container);

  class  Section_property_free_declarationContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * container;
    Section_property_free_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Section_property_free_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * container);
    virtual size_t getRuleIndex() const override;
    std::vector<Property_declarationContext *> property_declaration();
    Property_declarationContext* property_declaration(size_t i);

   
  };

  Section_property_free_declarationContext* section_property_free_declaration(sep::Machine * container);

  class  Property_declarationContext : public antlr4::ParserRuleContext {
  public:
    sep::PropertyPart * declPropertyPart;
    sep::Modifier mdfr;
    FMLParser::Modifier_declarationContext *m = nullptr;
    Property_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Property_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::PropertyPart * declPropertyPart, sep::Modifier mdfr);
    virtual size_t getRuleIndex() const override;
    Decl_property_elementContext *decl_property_element();
    Modifier_declarationContext *modifier_declaration();

   
  };

  Property_declarationContext* property_declaration(sep::PropertyPart * declPropertyPart,sep::Modifier mdfr);

  class  Decl_property_elementContext : public antlr4::ParserRuleContext {
  public:
    sep::PropertyPart * declPropertyPart;
    sep::Modifier mdfr;
    Decl_property_elementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Decl_property_elementContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::PropertyPart * declPropertyPart, sep::Modifier mdfr);
    virtual size_t getRuleIndex() const override;
    Decl_variableContext *decl_variable();
    Decl_portContext *decl_port();
    Decl_signalContext *decl_signal();
    Decl_bufferContext *decl_buffer();
    Decl_channelContext *decl_channel();
    Def_typeContext *def_type();
    Def_enumContext *def_enum();
    Def_unionContext *def_union();
    Def_choiceContext *def_choice();
    Def_structContext *def_struct();
    Decl_functionContext *decl_function();

   
  };

  Decl_property_elementContext* decl_property_element(sep::PropertyPart * declPropertyPart,sep::Modifier mdfr);

  class  Labelled_argumentContext : public antlr4::ParserRuleContext {
  public:
    std::string label;
    sep::BF arg;
    antlr4::Token *id = nullptr;
    FMLParser::ExpressionContext *e = nullptr;
    Labelled_argumentContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    ExpressionContext *expression();
    antlr4::tree::TerminalNode *COLON();
    antlr4::tree::TerminalNode *ID();

   
  };

  Labelled_argumentContext* labelled_argument();

  class  Decl_instance_machine_paramsContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * machine;
    FMLParser::Labelled_argumentContext *lp = nullptr;
    Decl_instance_machine_paramsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Decl_instance_machine_paramsContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * machine);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LPAREN();
    antlr4::tree::TerminalNode *RPAREN();
    std::vector<Labelled_argumentContext *> labelled_argument();
    Labelled_argumentContext* labelled_argument(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

   
  };

  Decl_instance_machine_paramsContext* decl_instance_machine_params(sep::Machine * machine);

  class  Decl_instance_machine_returnsContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * machine;
    FMLParser::Labelled_argumentContext *lp = nullptr;
    Decl_instance_machine_returnsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Decl_instance_machine_returnsContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * machine);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LPAREN();
    antlr4::tree::TerminalNode *RPAREN();
    std::vector<Labelled_argumentContext *> labelled_argument();
    Labelled_argumentContext* labelled_argument(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

   
  };

  Decl_instance_machine_returnsContext* decl_instance_machine_returns(sep::Machine * machine);

  class  Activity_machine_param_returnContext : public antlr4::ParserRuleContext {
  public:
    sep::BF argMachine;
    sep::BFCode ac;
    FMLParser::Labelled_argumentContext *lp = nullptr;
    Activity_machine_param_returnContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Activity_machine_param_returnContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::BF argMachine, sep::BFCode ac);
    virtual size_t getRuleIndex() const override;
    std::vector<antlr4::tree::TerminalNode *> LPAREN();
    antlr4::tree::TerminalNode* LPAREN(size_t i);
    std::vector<antlr4::tree::TerminalNode *> RPAREN();
    antlr4::tree::TerminalNode* RPAREN(size_t i);
    std::vector<Labelled_argumentContext *> labelled_argument();
    Labelled_argumentContext* labelled_argument(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

   
  };

  Activity_machine_param_returnContext* activity_machine_param_return(sep::BF argMachine,sep::BFCode ac);

  class  Decl_portContext : public antlr4::ParserRuleContext {
  public:
    sep::PropertyPart * declPropertyPart;
    sep::Modifier mdfr;
    Decl_portContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Decl_portContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::PropertyPart * declPropertyPart, sep::Modifier mdfr);
    virtual size_t getRuleIndex() const override;
    Decl_port_implContext *decl_port_impl();

   
  };

  Decl_portContext* decl_port(sep::PropertyPart * declPropertyPart,sep::Modifier mdfr);

  class  Decl_port_implContext : public antlr4::ParserRuleContext {
  public:
    sep::PropertyPart * declPropertyPart;
    sep::Modifier mdfr;
    sep::IComPoint::ENUM_IO_NATURE nature;
    antlr4::Token *id = nullptr;
    antlr4::Token *sl = nullptr;
    Decl_port_implContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Decl_port_implContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::PropertyPart * declPropertyPart, sep::Modifier mdfr, sep::IComPoint::ENUM_IO_NATURE nature);
    virtual size_t getRuleIndex() const override;
    std::vector<antlr4::tree::TerminalNode *> SEMI();
    antlr4::tree::TerminalNode* SEMI(size_t i);
    std::vector<antlr4::tree::TerminalNode *> ID();
    antlr4::tree::TerminalNode* ID(size_t i);
    std::vector<Typed_parameter_inputContext *> typed_parameter_input();
    Typed_parameter_inputContext* typed_parameter_input(size_t i);
    std::vector<antlr4::tree::TerminalNode *> StringLiteral();
    antlr4::tree::TerminalNode* StringLiteral(size_t i);
    std::vector<Modifier_set_direction_strict_textContext *> modifier_set_direction_strict_text();
    Modifier_set_direction_strict_textContext* modifier_set_direction_strict_text(size_t i);
    antlr4::tree::TerminalNode *LCURLY();
    antlr4::tree::TerminalNode *RCURLY();

   
  };

  Decl_port_implContext* decl_port_impl(sep::PropertyPart * declPropertyPart,sep::Modifier mdfr,sep::IComPoint::ENUM_IO_NATURE nature);

  class  Decl_signalContext : public antlr4::ParserRuleContext {
  public:
    sep::PropertyPart * declPropertyPart;
    sep::Modifier mdfr;
    Decl_signalContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Decl_signalContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::PropertyPart * declPropertyPart, sep::Modifier mdfr);
    virtual size_t getRuleIndex() const override;
    Decl_signal_implContext *decl_signal_impl();

   
  };

  Decl_signalContext* decl_signal(sep::PropertyPart * declPropertyPart,sep::Modifier mdfr);

  class  Decl_signal_implContext : public antlr4::ParserRuleContext {
  public:
    sep::PropertyPart * declPropertyPart;
    sep::Modifier mdfr;
    sep::IComPoint::ENUM_IO_NATURE nature;
    antlr4::Token *id = nullptr;
    antlr4::Token *sl = nullptr;
    Decl_signal_implContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Decl_signal_implContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::PropertyPart * declPropertyPart, sep::Modifier mdfr, sep::IComPoint::ENUM_IO_NATURE nature);
    virtual size_t getRuleIndex() const override;
    std::vector<antlr4::tree::TerminalNode *> SEMI();
    antlr4::tree::TerminalNode* SEMI(size_t i);
    std::vector<antlr4::tree::TerminalNode *> ID();
    antlr4::tree::TerminalNode* ID(size_t i);
    std::vector<Typed_parameter_inputContext *> typed_parameter_input();
    Typed_parameter_inputContext* typed_parameter_input(size_t i);
    std::vector<antlr4::tree::TerminalNode *> StringLiteral();
    antlr4::tree::TerminalNode* StringLiteral(size_t i);
    std::vector<Modifier_set_direction_strict_textContext *> modifier_set_direction_strict_text();
    Modifier_set_direction_strict_textContext* modifier_set_direction_strict_text(size_t i);
    antlr4::tree::TerminalNode *LCURLY();
    antlr4::tree::TerminalNode *RCURLY();

   
  };

  Decl_signal_implContext* decl_signal_impl(sep::PropertyPart * declPropertyPart,sep::Modifier mdfr,sep::IComPoint::ENUM_IO_NATURE nature);

  class  Typed_parameter_inputContext : public antlr4::ParserRuleContext {
  public:
    sep::PropertyPart * declParameterPart;
    Typed_parameter_inputContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Typed_parameter_inputContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::PropertyPart * declParameterPart);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LPAREN();
    std::vector<Typed_parameter_atomContext *> typed_parameter_atom();
    Typed_parameter_atomContext* typed_parameter_atom(size_t i);
    antlr4::tree::TerminalNode *RPAREN();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

   
  };

  Typed_parameter_inputContext* typed_parameter_input(sep::PropertyPart * declParameterPart);

  class  Typed_parameter_returnContext : public antlr4::ParserRuleContext {
  public:
    sep::PropertyPart * declParameterPart;
    Typed_parameter_returnContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Typed_parameter_returnContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::PropertyPart * declParameterPart);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LPAREN();
    std::vector<Typed_parameter_atomContext *> typed_parameter_atom();
    Typed_parameter_atomContext* typed_parameter_atom(size_t i);
    antlr4::tree::TerminalNode *RPAREN();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

   
  };

  Typed_parameter_returnContext* typed_parameter_return(sep::PropertyPart * declParameterPart);

  class  Typed_parameter_atomContext : public antlr4::ParserRuleContext {
  public:
    sep::PropertyPart * declParameterPart;
    sep::Modifier mdfr;
    sep::avm_offset_t offset;
    FMLParser::Type_varContext *tv = nullptr;
    antlr4::Token *id = nullptr;
    FMLParser::Initial_valueContext *iv = nullptr;
    FMLParser::ExpressionContext *e = nullptr;
    FMLParser::QualifiedNameIDContext *vid = nullptr;
    Typed_parameter_atomContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Typed_parameter_atomContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::PropertyPart * declParameterPart, sep::Modifier mdfr, sep::avm_offset_t offset);
    virtual size_t getRuleIndex() const override;
    Type_varContext *type_var();
    antlr4::tree::TerminalNode *ID();
    Initial_valueContext *initial_value();
    antlr4::tree::TerminalNode *COLON();
    ExpressionContext *expression();
    QualifiedNameIDContext *qualifiedNameID();

   
  };

  Typed_parameter_atomContext* typed_parameter_atom(sep::PropertyPart * declParameterPart,sep::Modifier mdfr,sep::avm_offset_t offset);

  class  Decl_bufferContext : public antlr4::ParserRuleContext {
  public:
    sep::PropertyPart * declPropertyPart;
    sep::Modifier mdfr;
    Decl_bufferContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Decl_bufferContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::PropertyPart * declPropertyPart, sep::Modifier mdfr);
    virtual size_t getRuleIndex() const override;
    Decl_buffer_implContext *decl_buffer_impl();

   
  };

  Decl_bufferContext* decl_buffer(sep::PropertyPart * declPropertyPart,sep::Modifier mdfr);

  class  Decl_buffer_implContext : public antlr4::ParserRuleContext {
  public:
    sep::PropertyPart * declPropertyPart;
    sep::Modifier mdfr;
    FMLParser::Def_bufferContext *db = nullptr;
    antlr4::Token *id = nullptr;
    Decl_buffer_implContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Decl_buffer_implContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::PropertyPart * declPropertyPart, sep::Modifier mdfr);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *SEMI();
    std::vector<Def_bufferContext *> def_buffer();
    Def_bufferContext* def_buffer(size_t i);
    std::vector<antlr4::tree::TerminalNode *> ID();
    antlr4::tree::TerminalNode* ID(size_t i);
    Initial_buffer_contentsContext *initial_buffer_contents();
    antlr4::tree::TerminalNode *LCURLY();
    antlr4::tree::TerminalNode *RCURLY();

   
  };

  Decl_buffer_implContext* decl_buffer_impl(sep::PropertyPart * declPropertyPart,sep::Modifier mdfr);

  class  Def_bufferContext : public antlr4::ParserRuleContext {
  public:
    sep::avm_type_specifier_kind_t kind;
    int size = -1;
    FMLParser::Policy_bufferContext *pb = nullptr;
    FMLParser::Integer_constantContext *n = nullptr;
    Def_bufferContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Policy_bufferContext *policy_buffer();
    antlr4::tree::TerminalNode *LT_();
    antlr4::tree::TerminalNode *GT();
    antlr4::tree::TerminalNode *LBRACKET();
    antlr4::tree::TerminalNode *RBRACKET();
    antlr4::tree::TerminalNode *STAR();
    Integer_constantContext *integer_constant();

   
  };

  Def_bufferContext* def_buffer();

  class  Policy_bufferContext : public antlr4::ParserRuleContext {
  public:
    sep::avm_type_specifier_kind_t kind;
    Policy_bufferContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;

   
  };

  Policy_bufferContext* policy_buffer();

  class  Ref_bufferContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * machine;
    sep::BF buf;
    FMLParser::QualifiedNameIDContext *id = nullptr;
    Ref_bufferContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Ref_bufferContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * machine);
    virtual size_t getRuleIndex() const override;
    QualifiedNameIDContext *qualifiedNameID();

   
  };

  Ref_bufferContext* ref_buffer(sep::Machine * machine);

  class  Initial_buffer_contentsContext : public antlr4::ParserRuleContext {
  public:
    const sep::Buffer * buffer;
    FMLParser::QualifiedNameIDContext *mid = nullptr;
    Initial_buffer_contentsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Initial_buffer_contentsContext(antlr4::ParserRuleContext *parent, size_t invokingState, const sep::Buffer * buffer);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ASSIGN();
    antlr4::tree::TerminalNode *LBRACKET();
    antlr4::tree::TerminalNode *RBRACKET();
    std::vector<QualifiedNameIDContext *> qualifiedNameID();
    QualifiedNameIDContext* qualifiedNameID(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

   
  };

  Initial_buffer_contentsContext* initial_buffer_contents(const sep::Buffer * buffer);

  class  Decl_channelContext : public antlr4::ParserRuleContext {
  public:
    sep::PropertyPart * declPropertyPart;
    sep::Modifier mdfr;
    Decl_channelContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Decl_channelContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::PropertyPart * declPropertyPart, sep::Modifier mdfr);
    virtual size_t getRuleIndex() const override;
    Decl_channel_portContext *decl_channel_port();

   
  };

  Decl_channelContext* decl_channel(sep::PropertyPart * declPropertyPart,sep::Modifier mdfr);

  class  Decl_channel_portContext : public antlr4::ParserRuleContext {
  public:
    sep::PropertyPart * declPropertyPart;
    sep::Modifier mdfr;
    antlr4::Token *id = nullptr;
    FMLParser::Modifier_directionContext *m = nullptr;
    FMLParser::QualifiedNameIDContext *uid = nullptr;
    Decl_channel_portContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Decl_channel_portContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::PropertyPart * declPropertyPart, sep::Modifier mdfr);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LCURLY();
    antlr4::tree::TerminalNode *RCURLY();
    antlr4::tree::TerminalNode *ID();
    antlr4::tree::TerminalNode *LT_();
    Com_protocolContext *com_protocol();
    antlr4::tree::TerminalNode *GT();
    Modifier_set_direction_strict_textContext *modifier_set_direction_strict_text();
    std::vector<antlr4::tree::TerminalNode *> SEMI();
    antlr4::tree::TerminalNode* SEMI(size_t i);
    std::vector<Decl_portContext *> decl_port();
    Decl_portContext* decl_port(size_t i);
    std::vector<Decl_signalContext *> decl_signal();
    Decl_signalContext* decl_signal(size_t i);
    std::vector<Modifier_directionContext *> modifier_direction();
    Modifier_directionContext* modifier_direction(size_t i);
    std::vector<QualifiedNameIDContext *> qualifiedNameID();
    QualifiedNameIDContext* qualifiedNameID(size_t i);
    antlr4::tree::TerminalNode *COMMA();
    Com_castContext *com_cast();

   
  };

  Decl_channel_portContext* decl_channel_port(sep::PropertyPart * declPropertyPart,sep::Modifier mdfr);

  class  Decl_channel_varContext : public antlr4::ParserRuleContext {
  public:
    sep::PropertyPart * declPropertyPart;
    sep::Modifier mdfr;
    FMLParser::Type_varContext *tv = nullptr;
    antlr4::Token *id = nullptr;
    FMLParser::Initial_valueContext *iv = nullptr;
    Decl_channel_varContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Decl_channel_varContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::PropertyPart * declPropertyPart, sep::Modifier mdfr);
    virtual size_t getRuleIndex() const override;
    std::vector<Type_varContext *> type_var();
    Type_varContext* type_var(size_t i);
    std::vector<antlr4::tree::TerminalNode *> ID();
    antlr4::tree::TerminalNode* ID(size_t i);
    std::vector<antlr4::tree::TerminalNode *> SEMI();
    antlr4::tree::TerminalNode* SEMI(size_t i);
    std::vector<On_write_var_routine_defContext *> on_write_var_routine_def();
    On_write_var_routine_defContext* on_write_var_routine_def(size_t i);
    std::vector<Initial_valueContext *> initial_value();
    Initial_valueContext* initial_value(size_t i);
    antlr4::tree::TerminalNode *LCURLY();
    antlr4::tree::TerminalNode *RCURLY();

   
  };

  Decl_channel_varContext* decl_channel_var(sep::PropertyPart * declPropertyPart,sep::Modifier mdfr);

  class  Decl_functionContext : public antlr4::ParserRuleContext {
  public:
    sep::PropertyPart * declPropertyPart;
    sep::Modifier mdfr;
    Decl_functionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Decl_functionContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::PropertyPart * declPropertyPart, sep::Modifier mdfr);
    virtual size_t getRuleIndex() const override;
    Decl_function_implContext *decl_function_impl();

   
  };

  Decl_functionContext* decl_function(sep::PropertyPart * declPropertyPart,sep::Modifier mdfr);

  class  Decl_function_implContext : public antlr4::ParserRuleContext {
  public:
    sep::PropertyPart * declPropertyPart;
    sep::Modifier mdfr;
    antlr4::Token *id = nullptr;
    Decl_function_implContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Decl_function_implContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::PropertyPart * declPropertyPart, sep::Modifier mdfr);
    virtual size_t getRuleIndex() const override;
    Typed_parameter_returnContext *typed_parameter_return();
    antlr4::tree::TerminalNode *SEMI();
    antlr4::tree::TerminalNode *ID();
    Typed_parameter_inputContext *typed_parameter_input();

   
  };

  Decl_function_implContext* decl_function_impl(sep::PropertyPart * declPropertyPart,sep::Modifier mdfr);

  class  Decl_variableContext : public antlr4::ParserRuleContext {
  public:
    sep::PropertyPart * declPropertyPart;
    sep::Modifier mdfr;
    Decl_variableContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Decl_variableContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::PropertyPart * declPropertyPart, sep::Modifier mdfr);
    virtual size_t getRuleIndex() const override;
    Decl_variable_implContext *decl_variable_impl();
    Decl_variable_time_clock_implContext *decl_variable_time_clock_impl();

   
  };

  Decl_variableContext* decl_variable(sep::PropertyPart * declPropertyPart,sep::Modifier mdfr);

  class  Decl_variable_time_clock_implContext : public antlr4::ParserRuleContext {
  public:
    sep::PropertyPart * declPropertyPart;
    sep::Modifier mdfr;
    FMLParser::Time_clock_typeContext *ctv = nullptr;
    Decl_variable_time_clock_implContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Decl_variable_time_clock_implContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::PropertyPart * declPropertyPart, sep::Modifier mdfr);
    virtual size_t getRuleIndex() const override;
    Decl_typed_variable_atom_implContext *decl_typed_variable_atom_impl();
    Time_clock_typeContext *time_clock_type();

   
  };

  Decl_variable_time_clock_implContext* decl_variable_time_clock_impl(sep::PropertyPart * declPropertyPart,sep::Modifier mdfr);

  class  Decl_variable_implContext : public antlr4::ParserRuleContext {
  public:
    sep::PropertyPart * declPropertyPart;
    sep::Modifier mdfr;
    Decl_variable_implContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Decl_variable_implContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::PropertyPart * declPropertyPart, sep::Modifier mdfr);
    virtual size_t getRuleIndex() const override;
    std::vector<Decl_variable_atom_implContext *> decl_variable_atom_impl();
    Decl_variable_atom_implContext* decl_variable_atom_impl(size_t i);
    antlr4::tree::TerminalNode *LCURLY();
    antlr4::tree::TerminalNode *RCURLY();

   
  };

  Decl_variable_implContext* decl_variable_impl(sep::PropertyPart * declPropertyPart,sep::Modifier mdfr);

  class  Decl_variable_atom_implContext : public antlr4::ParserRuleContext {
  public:
    sep::PropertyPart * declPropertyPart;
    sep::Modifier mdfr;
    FMLParser::Type_varContext *tv = nullptr;
    Decl_variable_atom_implContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Decl_variable_atom_implContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::PropertyPart * declPropertyPart, sep::Modifier mdfr);
    virtual size_t getRuleIndex() const override;
    Decl_typed_variable_atom_implContext *decl_typed_variable_atom_impl();
    Type_varContext *type_var();
    antlr4::tree::TerminalNode *BAND();

   
  };

  Decl_variable_atom_implContext* decl_variable_atom_impl(sep::PropertyPart * declPropertyPart,sep::Modifier mdfr);

  class  Decl_typed_variable_atom_implContext : public antlr4::ParserRuleContext {
  public:
    sep::PropertyPart * declPropertyPart;
    sep::Modifier mdfr;
    sep::BF type;
    antlr4::Token *id = nullptr;
    antlr4::Token *sl = nullptr;
    FMLParser::Initial_valueContext *iv = nullptr;
    Decl_typed_variable_atom_implContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Decl_typed_variable_atom_implContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::PropertyPart * declPropertyPart, sep::Modifier mdfr, sep::BF type);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ID();
    antlr4::tree::TerminalNode *SEMI();
    On_write_var_routine_defContext *on_write_var_routine_def();
    antlr4::tree::TerminalNode *StringLiteral();
    Initial_valueContext *initial_value();

   
  };

  Decl_typed_variable_atom_implContext* decl_typed_variable_atom_impl(sep::PropertyPart * declPropertyPart,sep::Modifier mdfr,sep::BF type);

  class  Initial_valueContext : public antlr4::ParserRuleContext {
  public:
    sep::BF bf;
    FMLParser::ExpressionContext *e = nullptr;
    Initial_valueContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ASSIGN();
    ExpressionContext *expression();
    antlr4::tree::TerminalNode *LPAREN();
    antlr4::tree::TerminalNode *RPAREN();

   
  };

  Initial_valueContext* initial_value();

  class  Type_varContext : public antlr4::ParserRuleContext {
  public:
    sep::BF type;
    FMLParser::Base_type_varContext *btv = nullptr;
    FMLParser::Def_type_arrayContext *dta = nullptr;
    FMLParser::Def_type_containerContext *dtc = nullptr;
    FMLParser::Def_type_intervalContext *dti = nullptr;
    Type_varContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Base_type_varContext *base_type_var();
    Def_type_arrayContext *def_type_array();
    Def_type_containerContext *def_type_container();
    Def_type_intervalContext *def_type_interval();

   
  };

  Type_varContext* type_var();

  class  Def_type_arrayContext : public antlr4::ParserRuleContext {
  public:
    sep::BF baseT;
    std::string tid;
    sep::BF type;
    FMLParser::Def_type_array_sizeContext *dta = nullptr;
    Def_type_arrayContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_type_arrayContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::BF baseT, std::string tid);
    virtual size_t getRuleIndex() const override;
    std::vector<Def_type_array_sizeContext *> def_type_array_size();
    Def_type_array_sizeContext* def_type_array_size(size_t i);

   
  };

  Def_type_arrayContext* def_type_array(sep::BF baseT,std::string tid);

  class  Def_type_array_sizeContext : public antlr4::ParserRuleContext {
  public:
    int size;
    antlr4::Token *sz = nullptr;
    FMLParser::QualifiedNameIDContext *id = nullptr;
    Def_type_array_sizeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LBRACKET();
    antlr4::tree::TerminalNode *RBRACKET();
    antlr4::tree::TerminalNode *IntegerLiteral();
    QualifiedNameIDContext *qualifiedNameID();

   
  };

  Def_type_array_sizeContext* def_type_array_size();

  class  Def_type_containerContext : public antlr4::ParserRuleContext {
  public:
    std::string tid;
    sep::BF type;
    FMLParser::Specifier_bufferContext *sb = nullptr;
    FMLParser::Base_type_varContext *btv = nullptr;
    FMLParser::Integer_constantContext *sz = nullptr;
    Def_type_containerContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_type_containerContext(antlr4::ParserRuleContext *parent, size_t invokingState, std::string tid);
    virtual size_t getRuleIndex() const override;
    Specifier_bufferContext *specifier_buffer();
    antlr4::tree::TerminalNode *LT_();
    antlr4::tree::TerminalNode *GT();
    Integer_constantContext *integer_constant();
    Base_type_varContext *base_type_var();
    antlr4::tree::TerminalNode *COMMA();
    antlr4::tree::TerminalNode *STAR();

   
  };

  Def_type_containerContext* def_type_container(std::string tid);

  class  Specifier_bufferContext : public antlr4::ParserRuleContext {
  public:
    sep::avm_type_specifier_kind_t kind;
    Specifier_bufferContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;

   
  };

  Specifier_bufferContext* specifier_buffer();

  class  Def_type_intervalContext : public antlr4::ParserRuleContext {
  public:
    std::string tid;
    sep::BF type;
    FMLParser::Primitive_typeContext *pt = nullptr;
    antlr4::Token *ll = nullptr;
    FMLParser::ExpressionContext *min = nullptr;
    FMLParser::ExpressionContext *max = nullptr;
    antlr4::Token *rr = nullptr;
    Def_type_intervalContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_type_intervalContext(antlr4::ParserRuleContext *parent, size_t invokingState, std::string tid);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LT_();
    antlr4::tree::TerminalNode *COMMA();
    antlr4::tree::TerminalNode *GT();
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> LBRACKET();
    antlr4::tree::TerminalNode* LBRACKET(size_t i);
    std::vector<antlr4::tree::TerminalNode *> RBRACKET();
    antlr4::tree::TerminalNode* RBRACKET(size_t i);
    antlr4::tree::TerminalNode *LPAREN();
    antlr4::tree::TerminalNode *RPAREN();
    Primitive_typeContext *primitive_type();

   
  };

  Def_type_intervalContext* def_type_interval(std::string tid);

  class  Base_type_varContext : public antlr4::ParserRuleContext {
  public:
    sep::BF type;
    FMLParser::Primitive_typeContext *pt = nullptr;
    FMLParser::QualifiedNameIDContext *id = nullptr;
    Base_type_varContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Primitive_typeContext *primitive_type();
    QualifiedNameIDContext *qualifiedNameID();

   
  };

  Base_type_varContext* base_type_var();

  class  Primitive_typeContext : public antlr4::ParserRuleContext {
  public:
    sep::TypeSpecifier bts;
    FMLParser::Bit_field_sizeContext *bfs = nullptr;
    FMLParser::Time_clock_typeContext *ct = nullptr;
    FMLParser::Time_typeContext *tt = nullptr;
    FMLParser::String_field_sizeContext *sfs = nullptr;
    FMLParser::QualifiedNameIDContext *id = nullptr;
    Primitive_typeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Bit_field_sizeContext *bit_field_size();
    Time_clock_typeContext *time_clock_type();
    Time_typeContext *time_type();
    String_field_sizeContext *string_field_size();
    antlr4::tree::TerminalNode *LT_();
    antlr4::tree::TerminalNode *GT();
    QualifiedNameIDContext *qualifiedNameID();

   
  };

  Primitive_typeContext* primitive_type();

  class  Bit_field_sizeContext : public antlr4::ParserRuleContext {
  public:
    int size;
    FMLParser::Integer_constantContext *n = nullptr;
    Bit_field_sizeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *COLON();
    Integer_constantContext *integer_constant();
    antlr4::tree::TerminalNode *LT_();
    antlr4::tree::TerminalNode *GT();

   
  };

  Bit_field_sizeContext* bit_field_size();

  class  String_field_sizeContext : public antlr4::ParserRuleContext {
  public:
    int min = 0;
    int max = -1;
    FMLParser::Range_constantContext *rc = nullptr;
    String_field_sizeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *COLON();
    Range_constantContext *range_constant();
    antlr4::tree::TerminalNode *LT_();
    antlr4::tree::TerminalNode *GT();

   
  };

  String_field_sizeContext* string_field_size();

  class  Range_constantContext : public antlr4::ParserRuleContext {
  public:
    int min = 0;
    int max = -1;
    FMLParser::Integer_constantContext *n = nullptr;
    Range_constantContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Integer_constantContext *> integer_constant();
    Integer_constantContext* integer_constant(size_t i);
    antlr4::tree::TerminalNode *COMMA();
    antlr4::tree::TerminalNode *DOTDOT();

   
  };

  Range_constantContext* range_constant();

  class  On_write_var_routine_defContext : public antlr4::ParserRuleContext {
  public:
    sep::Variable * var;
    On_write_var_routine_defContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    On_write_var_routine_defContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Variable * var);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LCURLY();
    antlr4::tree::TerminalNode *RCURLY();
    std::vector<Var_routine_defContext *> var_routine_def();
    Var_routine_defContext* var_routine_def(size_t i);

   
  };

  On_write_var_routine_defContext* on_write_var_routine_def(sep::Variable * var);

  class  Var_routine_defContext : public antlr4::ParserRuleContext {
  public:
    sep::Variable * var;
    FMLParser::Block_statementContext *bs = nullptr;
    FMLParser::ConditionalExpressionContext *ce = nullptr;
    Var_routine_defContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Var_routine_defContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Variable * var);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *SEMI();
    Routine_single_paramContext *routine_single_param();
    Block_statementContext *block_statement();
    ConditionalExpressionContext *conditionalExpression();

   
  };

  Var_routine_defContext* var_routine_def(sep::Variable * var);

  class  Routine_single_paramContext : public antlr4::ParserRuleContext {
  public:
    sep::Routine * routine;
    sep::BF dftType;
    FMLParser::Type_varContext *tv = nullptr;
    antlr4::Token *id = nullptr;
    FMLParser::Initial_valueContext *iv = nullptr;
    Routine_single_paramContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Routine_single_paramContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Routine * routine, sep::BF dftType);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LPAREN();
    antlr4::tree::TerminalNode *RPAREN();
    Type_varContext *type_var();
    antlr4::tree::TerminalNode *ID();
    Initial_valueContext *initial_value();

   
  };

  Routine_single_paramContext* routine_single_param(sep::Routine * routine,sep::BF dftType);

  class  Def_enumContext : public antlr4::ParserRuleContext {
  public:
    sep::PropertyPart * declPropertyPart;
    sep::Modifier mdfr;
    antlr4::Token *id = nullptr;
    Def_enumContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_enumContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::PropertyPart * declPropertyPart, sep::Modifier mdfr);
    virtual size_t getRuleIndex() const override;
    Def_enum_implContext *def_enum_impl();
    antlr4::tree::TerminalNode *ID();

   
  };

  Def_enumContext* def_enum(sep::PropertyPart * declPropertyPart,sep::Modifier mdfr);

  class  Def_enum_implContext : public antlr4::ParserRuleContext {
  public:
    sep::PropertyPart * declPropertyPart;
    sep::Modifier mdfr;
    std::string tid;
    antlr4::Token *id = nullptr;
    antlr4::Token *sl = nullptr;
    FMLParser::ExpressionContext *e = nullptr;
    antlr4::Token *superId = nullptr;
    Def_enum_implContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_enum_implContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::PropertyPart * declPropertyPart, sep::Modifier mdfr, std::string tid);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LCURLY();
    antlr4::tree::TerminalNode *RCURLY();
    std::vector<antlr4::tree::TerminalNode *> ID();
    antlr4::tree::TerminalNode* ID(size_t i);
    std::vector<antlr4::tree::TerminalNode *> ASSIGN();
    antlr4::tree::TerminalNode* ASSIGN(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    std::vector<antlr4::tree::TerminalNode *> StringLiteral();
    antlr4::tree::TerminalNode* StringLiteral(size_t i);
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);
    antlr4::tree::TerminalNode *LT_();
    antlr4::tree::TerminalNode *GT();

   
  };

  Def_enum_implContext* def_enum_impl(sep::PropertyPart * declPropertyPart,sep::Modifier mdfr,std::string tid);

  class  Def_structContext : public antlr4::ParserRuleContext {
  public:
    sep::PropertyPart * declPropertyPart;
    sep::Modifier mdfr;
    antlr4::Token *id = nullptr;
    Def_structContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_structContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::PropertyPart * declPropertyPart, sep::Modifier mdfr);
    virtual size_t getRuleIndex() const override;
    Def_class_structure_implContext *def_class_structure_impl();
    antlr4::tree::TerminalNode *ID();

   
  };

  Def_structContext* def_struct(sep::PropertyPart * declPropertyPart,sep::Modifier mdfr);

  class  Def_class_structure_implContext : public antlr4::ParserRuleContext {
  public:
    sep::PropertyPart * declPropertyPart;
    sep::Modifier mdfr;
    std::string tid;
    FMLParser::Modifier_declarationContext *m = nullptr;
    Def_class_structure_implContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_class_structure_implContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::PropertyPart * declPropertyPart, sep::Modifier mdfr, std::string tid);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LCURLY();
    antlr4::tree::TerminalNode *RCURLY();
    std::vector<Decl_variableContext *> decl_variable();
    Decl_variableContext* decl_variable(size_t i);
    std::vector<Modifier_declarationContext *> modifier_declaration();
    Modifier_declarationContext* modifier_declaration(size_t i);

   
  };

  Def_class_structure_implContext* def_class_structure_impl(sep::PropertyPart * declPropertyPart,sep::Modifier mdfr,std::string tid);

  class  Def_choiceContext : public antlr4::ParserRuleContext {
  public:
    sep::PropertyPart * declPropertyPart;
    sep::Modifier mdfr;
    antlr4::Token *id = nullptr;
    Def_choiceContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_choiceContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::PropertyPart * declPropertyPart, sep::Modifier mdfr);
    virtual size_t getRuleIndex() const override;
    Def_choice_implContext *def_choice_impl();
    antlr4::tree::TerminalNode *ID();

   
  };

  Def_choiceContext* def_choice(sep::PropertyPart * declPropertyPart,sep::Modifier mdfr);

  class  Def_choice_implContext : public antlr4::ParserRuleContext {
  public:
    sep::PropertyPart * declPropertyPart;
    sep::Modifier mdfr;
    std::string tid;
    FMLParser::Modifier_declarationContext *m = nullptr;
    Def_choice_implContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_choice_implContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::PropertyPart * declPropertyPart, sep::Modifier mdfr, std::string tid);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LCURLY();
    antlr4::tree::TerminalNode *RCURLY();
    std::vector<Decl_variableContext *> decl_variable();
    Decl_variableContext* decl_variable(size_t i);
    std::vector<Modifier_declarationContext *> modifier_declaration();
    Modifier_declarationContext* modifier_declaration(size_t i);

   
  };

  Def_choice_implContext* def_choice_impl(sep::PropertyPart * declPropertyPart,sep::Modifier mdfr,std::string tid);

  class  Def_unionContext : public antlr4::ParserRuleContext {
  public:
    sep::PropertyPart * declPropertyPart;
    sep::Modifier mdfr;
    antlr4::Token *id = nullptr;
    Def_unionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_unionContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::PropertyPart * declPropertyPart, sep::Modifier mdfr);
    virtual size_t getRuleIndex() const override;
    Def_union_implContext *def_union_impl();
    antlr4::tree::TerminalNode *ID();

   
  };

  Def_unionContext* def_union(sep::PropertyPart * declPropertyPart,sep::Modifier mdfr);

  class  Def_union_implContext : public antlr4::ParserRuleContext {
  public:
    sep::PropertyPart * declPropertyPart;
    sep::Modifier mdfr;
    std::string tid;
    FMLParser::Modifier_declarationContext *m = nullptr;
    Def_union_implContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_union_implContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::PropertyPart * declPropertyPart, sep::Modifier mdfr, std::string tid);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LCURLY();
    antlr4::tree::TerminalNode *RCURLY();
    std::vector<Decl_variableContext *> decl_variable();
    Decl_variableContext* decl_variable(size_t i);
    std::vector<Modifier_declarationContext *> modifier_declaration();
    Modifier_declarationContext* modifier_declaration(size_t i);

   
  };

  Def_union_implContext* def_union_impl(sep::PropertyPart * declPropertyPart,sep::Modifier mdfr,std::string tid);

  class  Def_typeContext : public antlr4::ParserRuleContext {
  public:
    sep::PropertyPart * declPropertyPart;
    sep::Modifier mdfr;
    Def_typeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_typeContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::PropertyPart * declPropertyPart, sep::Modifier mdfr);
    virtual size_t getRuleIndex() const override;
    Def_type_implContext *def_type_impl();

   
  };

  Def_typeContext* def_type(sep::PropertyPart * declPropertyPart,sep::Modifier mdfr);

  class  Def_type_implContext : public antlr4::ParserRuleContext {
  public:
    sep::PropertyPart * declPropertyPart;
    sep::Modifier mdfr;
    Def_type_implContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_type_implContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::PropertyPart * declPropertyPart, sep::Modifier mdfr);
    virtual size_t getRuleIndex() const override;
    std::vector<Def_type_atom_implContext *> def_type_atom_impl();
    Def_type_atom_implContext* def_type_atom_impl(size_t i);
    antlr4::tree::TerminalNode *LCURLY();
    antlr4::tree::TerminalNode *RCURLY();

   
  };

  Def_type_implContext* def_type_impl(sep::PropertyPart * declPropertyPart,sep::Modifier mdfr);

  class  Def_type_atom_implContext : public antlr4::ParserRuleContext {
  public:
    sep::PropertyPart * declPropertyPart;
    sep::Modifier mdfr;
    antlr4::Token *id = nullptr;
    FMLParser::Base_type_varContext *btv = nullptr;
    FMLParser::Def_type_arrayContext *dta = nullptr;
    FMLParser::Def_type_containerContext *dtc = nullptr;
    FMLParser::Def_type_intervalContext *dti = nullptr;
    Def_type_atom_implContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_type_atom_implContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::PropertyPart * declPropertyPart, sep::Modifier mdfr);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ID();
    antlr4::tree::TerminalNode *SEMI();
    Def_enum_implContext *def_enum_impl();
    Def_union_implContext *def_union_impl();
    Def_choice_implContext *def_choice_impl();
    Def_class_structure_implContext *def_class_structure_impl();
    Base_type_varContext *base_type_var();
    Def_type_containerContext *def_type_container();
    Def_type_intervalContext *def_type_interval();
    Def_typedef_constraintContext *def_typedef_constraint();
    Def_type_arrayContext *def_type_array();
    Def_enumContext *def_enum();
    Def_unionContext *def_union();
    Def_choiceContext *def_choice();
    Def_structContext *def_struct();

   
  };

  Def_type_atom_implContext* def_type_atom_impl(sep::PropertyPart * declPropertyPart,sep::Modifier mdfr);

  class  Def_typedef_constraintContext : public antlr4::ParserRuleContext {
  public:
    sep::DataType * aliasT;
    FMLParser::Block_statementContext *bs = nullptr;
    FMLParser::ConditionalExpressionContext *ce = nullptr;
    Def_typedef_constraintContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_typedef_constraintContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::DataType * aliasT);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LCURLY();
    antlr4::tree::TerminalNode *RCURLY();
    antlr4::tree::TerminalNode *SEMI();
    Routine_single_paramContext *routine_single_param();
    Block_statementContext *block_statement();
    ConditionalExpressionContext *conditionalExpression();

   
  };

  Def_typedef_constraintContext* def_typedef_constraint(sep::DataType * aliasT);

  class  Time_typeContext : public antlr4::ParserRuleContext {
  public:
    sep::TypeSpecifier bts;
    FMLParser::Time_type_domainContext *pt = nullptr;
    FMLParser::Integer_constantContext *sz = nullptr;
    Time_typeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LT_();
    antlr4::tree::TerminalNode *GT();
    Time_type_domainContext *time_type_domain();
    antlr4::tree::TerminalNode *COMMA();
    Integer_constantContext *integer_constant();

   
  };

  Time_typeContext* time_type();

  class  Time_clock_typeContext : public antlr4::ParserRuleContext {
  public:
    sep::TypeSpecifier bts;
    FMLParser::Time_type_domainContext *pt = nullptr;
    FMLParser::Integer_constantContext *sz = nullptr;
    Time_clock_typeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LT_();
    antlr4::tree::TerminalNode *GT();
    Time_type_domainContext *time_type_domain();
    antlr4::tree::TerminalNode *COMMA();
    Integer_constantContext *integer_constant();

   
  };

  Time_clock_typeContext* time_clock_type();

  class  Time_type_domainContext : public antlr4::ParserRuleContext {
  public:
    sep::TypeSpecifier type;
    FMLParser::Integer_constantContext *n = nullptr;
    Time_type_domainContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LT_();
    antlr4::tree::TerminalNode *GT();
    Integer_constantContext *integer_constant();

   
  };

  Time_type_domainContext* time_type_domain();

  class  Section_model_of_computationContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * container;
    Section_model_of_computationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Section_model_of_computationContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * container);
    virtual size_t getRuleIndex() const override;

   
  };

  Section_model_of_computationContext* section_model_of_computation(sep::Machine * container);

  class  Section_routineContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * container;
    Section_routineContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Section_routineContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * container);
    virtual size_t getRuleIndex() const override;
    std::vector<Def_routine_modelContext *> def_routine_model();
    Def_routine_modelContext* def_routine_model(size_t i);

   
  };

  Section_routineContext* section_routine(sep::Machine * container);

  class  Def_routine_modelContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * container;
    sep::Modifier mdfr;
    sep::Specifier spcfr;
    Def_routine_modelContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_routine_modelContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * container, sep::Modifier mdfr, sep::Specifier spcfr);
    virtual size_t getRuleIndex() const override;
    Def_routine_model_implContext *def_routine_model_impl();

   
  };

  Def_routine_modelContext* def_routine_model(sep::Machine * container,sep::Modifier mdfr,sep::Specifier spcfr);

  class  Def_routine_model_implContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * container;
    sep::Modifier mdfr;
    sep::Specifier spcfr;
    antlr4::Token *idToken = nullptr;
    FMLParser::Block_statementContext *bs = nullptr;
    Def_routine_model_implContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_routine_model_implContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * container, sep::Modifier mdfr, sep::Specifier spcfr);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ID();
    Block_statementContext *block_statement();
    Def_routine_parametersContext *def_routine_parameters();
    Def_routine_returnsContext *def_routine_returns();

   
  };

  Def_routine_model_implContext* def_routine_model_impl(sep::Machine * container,sep::Modifier mdfr,sep::Specifier spcfr);

  class  Def_routine_parametersContext : public antlr4::ParserRuleContext {
  public:
    sep::Routine * routine;
    Def_routine_parametersContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_routine_parametersContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Routine * routine);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LPAREN();
    antlr4::tree::TerminalNode *RPAREN();
    std::vector<Def_routine_param_atomContext *> def_routine_param_atom();
    Def_routine_param_atomContext* def_routine_param_atom(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

   
  };

  Def_routine_parametersContext* def_routine_parameters(sep::Routine * routine);

  class  Def_routine_param_atomContext : public antlr4::ParserRuleContext {
  public:
    sep::Routine * routine;
    std::size_t offset;
    FMLParser::Modifier_paramContext *m = nullptr;
    FMLParser::Type_varContext *tv = nullptr;
    antlr4::Token *id = nullptr;
    FMLParser::Initial_valueContext *iv = nullptr;
    Def_routine_param_atomContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_routine_param_atomContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Routine * routine, std::size_t offset);
    virtual size_t getRuleIndex() const override;
    Type_varContext *type_var();
    antlr4::tree::TerminalNode *ID();
    Initial_valueContext *initial_value();
    Modifier_paramContext *modifier_param();

   
  };

  Def_routine_param_atomContext* def_routine_param_atom(sep::Routine * routine,std::size_t offset);

  class  Def_routine_returnsContext : public antlr4::ParserRuleContext {
  public:
    sep::Routine * routine;
    FMLParser::Type_varContext *tv = nullptr;
    FMLParser::Initial_valueContext *iv = nullptr;
    Def_routine_returnsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_routine_returnsContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Routine * routine);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LPAREN();
    std::vector<Def_routine_returns_atomContext *> def_routine_returns_atom();
    Def_routine_returns_atomContext* def_routine_returns_atom(size_t i);
    antlr4::tree::TerminalNode *RPAREN();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    Type_varContext *type_var();
    Initial_valueContext *initial_value();

   
  };

  Def_routine_returnsContext* def_routine_returns(sep::Routine * routine);

  class  Def_routine_returns_atomContext : public antlr4::ParserRuleContext {
  public:
    sep::Routine * routine;
    std::size_t offset;
    FMLParser::Modifier_paramContext *m = nullptr;
    FMLParser::Type_varContext *tv = nullptr;
    antlr4::Token *id = nullptr;
    FMLParser::Initial_valueContext *iv = nullptr;
    Def_routine_returns_atomContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_routine_returns_atomContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Routine * routine, std::size_t offset);
    virtual size_t getRuleIndex() const override;
    Type_varContext *type_var();
    antlr4::tree::TerminalNode *ID();
    Initial_valueContext *initial_value();
    Modifier_paramContext *modifier_param();

   
  };

  Def_routine_returns_atomContext* def_routine_returns_atom(sep::Routine * routine,std::size_t offset);

  class  Section_model_of_executionContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * container;
    Section_model_of_executionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Section_model_of_executionContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * container);
    virtual size_t getRuleIndex() const override;
    std::vector<Def_moe_primitiveContext *> def_moe_primitive();
    Def_moe_primitiveContext* def_moe_primitive(size_t i);

   
  };

  Section_model_of_executionContext* section_model_of_execution(sep::Machine * container);

  class  Def_moe_primitiveContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * container;
    Def_moe_primitiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_moe_primitiveContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * container);
    virtual size_t getRuleIndex() const override;
    Def_routine_seqContext *def_routine_seq();
    Def_routine_model_implContext *def_routine_model_impl();

   
  };

  Def_moe_primitiveContext* def_moe_primitive(sep::Machine * container);

  class  Def_routine_seqContext : public antlr4::ParserRuleContext {
  public:
    sep::Routine * routine;
    FMLParser::Block_statementContext *bs = nullptr;
    Def_routine_seqContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Def_routine_seqContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Routine * routine);
    virtual size_t getRuleIndex() const override;
    Block_statementContext *block_statement();
    Def_routine_parametersContext *def_routine_parameters();
    Def_routine_returnsContext *def_routine_returns();

   
  };

  Def_routine_seqContext* def_routine_seq(sep::Routine * routine);

  class  Section_model_of_interactionContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * machine;
    Section_model_of_interactionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Section_model_of_interactionContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * machine);
    virtual size_t getRuleIndex() const override;
    std::vector<Com_connectorContext *> com_connector();
    Com_connectorContext* com_connector(size_t i);

   
  };

  Section_model_of_interactionContext* section_model_of_interaction(sep::Machine * machine);

  class  Com_protocolContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * machine;
    sep::ComProtocol * cp;
    FMLParser::Buffer_comContext *bc = nullptr;
    Com_protocolContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Com_protocolContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * machine, sep::ComProtocol * cp);
    virtual size_t getRuleIndex() const override;
    Buffer_comContext *buffer_com();

   
  };

  Com_protocolContext* com_protocol(sep::Machine * machine,sep::ComProtocol * cp);

  class  Com_castContext : public antlr4::ParserRuleContext {
  public:
    sep::ComProtocol * cp;
    Com_castContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Com_castContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::ComProtocol * cp);
    virtual size_t getRuleIndex() const override;

   
  };

  Com_castContext* com_cast(sep::ComProtocol * cp);

  class  Buffer_comContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * machine;
    sep::BF buf;
    FMLParser::Ref_bufferContext *rb = nullptr;
    FMLParser::Def_bufferContext *db = nullptr;
    Buffer_comContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Buffer_comContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * machine);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *COLON();
    antlr4::tree::TerminalNode *LT_();
    antlr4::tree::TerminalNode *GT();
    Ref_bufferContext *ref_buffer();
    Def_bufferContext *def_buffer();

   
  };

  Buffer_comContext* buffer_com(sep::Machine * machine);

  class  Com_connectorContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * machine;
    sep::InteractionPart * anInteractionPart;
    antlr4::Token *idToken = nullptr;
    Com_connectorContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Com_connectorContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * machine, sep::InteractionPart * anInteractionPart);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LCURLY();
    antlr4::tree::TerminalNode *RCURLY();
    antlr4::tree::TerminalNode *LT_();
    Com_protocolContext *com_protocol();
    antlr4::tree::TerminalNode *GT();
    antlr4::tree::TerminalNode *ID();
    std::vector<Com_routeContext *> com_route();
    Com_routeContext* com_route(size_t i);
    antlr4::tree::TerminalNode *COMMA();
    Com_castContext *com_cast();
    antlr4::tree::TerminalNode *LBRACKET();
    Com_route_pointsContext *com_route_points();
    antlr4::tree::TerminalNode *RBRACKET();
    antlr4::tree::TerminalNode *SEMI();

   
  };

  Com_connectorContext* com_connector(sep::Machine * machine,sep::InteractionPart * anInteractionPart);

  class  Com_routeContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * machine;
    sep::Connector * aConnector;
    FMLParser::Buffer_comContext *bc = nullptr;
    Com_routeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Com_routeContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * machine, sep::Connector * aConnector);
    virtual size_t getRuleIndex() const override;
    Modifier_set_direction_strict_textContext *modifier_set_direction_strict_text();
    std::vector<Com_portContext *> com_port();
    Com_portContext* com_port(size_t i);
    std::vector<antlr4::tree::TerminalNode *> SEMI();
    antlr4::tree::TerminalNode* SEMI(size_t i);
    antlr4::tree::TerminalNode *LCURLY();
    antlr4::tree::TerminalNode *RCURLY();
    antlr4::tree::TerminalNode *LBRACKET();
    antlr4::tree::TerminalNode *RBRACKET();
    antlr4::tree::TerminalNode *LT_();
    antlr4::tree::TerminalNode *GT();
    antlr4::tree::TerminalNode *STAR();
    Com_castContext *com_cast();
    Buffer_comContext *buffer_com();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

   
  };

  Com_routeContext* com_route(sep::Machine * machine,sep::Connector * aConnector);

  class  Com_route_pointsContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * machine;
    sep::Connector * aConnector;
    Com_route_pointsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Com_route_pointsContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * machine, sep::Connector * aConnector);
    virtual size_t getRuleIndex() const override;
    std::vector<Com_portContext *> com_port();
    Com_portContext* com_port(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    antlr4::tree::TerminalNode *STAR();

   
  };

  Com_route_pointsContext* com_route_points(sep::Machine * machine,sep::Connector * aConnector);

  class  Com_portContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * machine;
    sep::ComRoute * comRoute;
    FMLParser::QualifiedNameIDContext *m = nullptr;
    FMLParser::QualifiedNameIDContext *id = nullptr;
    Com_portContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Com_portContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * machine, sep::ComRoute * comRoute);
    virtual size_t getRuleIndex() const override;
    QualifiedNameIDContext *qualifiedNameID();
    std::vector<Com_port_idContext *> com_port_id();
    Com_port_idContext* com_port_id(size_t i);
    antlr4::tree::TerminalNode *LBRACKET();
    antlr4::tree::TerminalNode *RBRACKET();
    antlr4::tree::TerminalNode *STAR();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

   
  };

  Com_portContext* com_port(sep::Machine * machine,sep::ComRoute * comRoute);

  class  Com_port_idContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * machine;
    sep::ComRoute * comRoute;
    sep::Machine * comMachine;
    FMLParser::QualifiedNameIDContext *id = nullptr;
    Com_port_idContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Com_port_idContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * machine, sep::ComRoute * comRoute, sep::Machine * comMachine);
    virtual size_t getRuleIndex() const override;
    QualifiedNameIDContext *qualifiedNameID();

   
  };

  Com_port_idContext* com_port_id(sep::Machine * machine,sep::ComRoute * comRoute,sep::Machine * comMachine);

  class  StatementContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    FMLParser::Statement_assignContext *s01 = nullptr;
    FMLParser::Statement_comContext *s03 = nullptr;
    FMLParser::Statement_constraintContext *s04 = nullptr;
    FMLParser::Statement_jumpContext *s05 = nullptr;
    FMLParser::Statement_activityContext *s07 = nullptr;
    FMLParser::Statement_invoke_routineContext *s08 = nullptr;
    FMLParser::Statement_mocContext *s09 = nullptr;
    FMLParser::Statement_invokeContext *s10 = nullptr;
    FMLParser::Statement_invoke_methodContext *s11 = nullptr;
    FMLParser::Statement_activity_newContext *s12 = nullptr;
    FMLParser::Statement_iteContext *s13 = nullptr;
    FMLParser::Statement_iterationContext *s14 = nullptr;
    FMLParser::Block_statementContext *s16 = nullptr;
    FMLParser::Prefix_statementContext *s17 = nullptr;
    FMLParser::Statement_promptContext *s18 = nullptr;
    FMLParser::Meta_statementContext *s19 = nullptr;
    StatementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Statement_assignContext *statement_assign();
    Statement_comContext *statement_com();
    Statement_constraintContext *statement_constraint();
    Statement_jumpContext *statement_jump();
    Statement_activityContext *statement_activity();
    Statement_invoke_routineContext *statement_invoke_routine();
    Statement_mocContext *statement_moc();
    Statement_invokeContext *statement_invoke();
    Statement_invoke_methodContext *statement_invoke_method();
    Statement_activity_newContext *statement_activity_new();
    Statement_iteContext *statement_ite();
    Statement_iterationContext *statement_iteration();
    Block_statementContext *block_statement();
    Prefix_statementContext *prefix_statement();
    Statement_promptContext *statement_prompt();
    Meta_statementContext *meta_statement();

   
  };

  StatementContext* statement();

  class  Block_statementContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    FMLParser::Op_blockContext *o = nullptr;
    FMLParser::StatementContext *s = nullptr;
    Block_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LCURLY();
    antlr4::tree::TerminalNode *RCURLY();
    Op_blockContext *op_block();
    std::vector<StatementContext *> statement();
    StatementContext* statement(size_t i);

   
  };

  Block_statementContext* block_statement();

  class  Op_blockContext : public antlr4::ParserRuleContext {
  public:
    const sep::Operator * op;
    FMLParser::Op_sequenceContext *o1 = nullptr;
    FMLParser::Op_schedulingContext *o2 = nullptr;
    FMLParser::Op_concurrencyContext *o3 = nullptr;
    Op_blockContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Op_sequenceContext *op_sequence();
    Op_schedulingContext *op_scheduling();
    Op_concurrencyContext *op_concurrency();
    antlr4::tree::TerminalNode *OP_FORK();
    antlr4::tree::TerminalNode *OP_JOIN();

   
  };

  Op_blockContext* op_block();

  class  Op_sequenceContext : public antlr4::ParserRuleContext {
  public:
    const sep::Operator * op;
    Op_sequenceContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OP_SEQUENCE();
    antlr4::tree::TerminalNode *OP_SEQUENCE_SIDE();
    antlr4::tree::TerminalNode *OP_SEQUENCE_WEAK();
    antlr4::tree::TerminalNode *OP_ATOMIC_SEQUENCE();

   
  };

  Op_sequenceContext* op_sequence();

  class  Op_schedulingContext : public antlr4::ParserRuleContext {
  public:
    const sep::Operator * op;
    Op_schedulingContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OP_SCHEDULE_GT();
    antlr4::tree::TerminalNode *OP_SCHEDULE_LT();
    antlr4::tree::TerminalNode *OP_SCHEDULE_XOR();
    antlr4::tree::TerminalNode *OP_SCHEDULE_AND_THEN();
    antlr4::tree::TerminalNode *OP_SCHEDULE_OR_ELSE();
    antlr4::tree::TerminalNode *OP_NON_DETERMINISM();

   
  };

  Op_schedulingContext* op_scheduling();

  class  Op_concurrencyContext : public antlr4::ParserRuleContext {
  public:
    const sep::Operator * op;
    Op_concurrencyContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OP_CONCURRENCY_ASYNC();
    antlr4::tree::TerminalNode *OP_CONCURRENCY_AND();
    antlr4::tree::TerminalNode *OP_CONCURRENCY_OR();
    antlr4::tree::TerminalNode *OP_CONCURRENCY_INTERLEAVING();
    antlr4::tree::TerminalNode *OP_CONCURRENCY_PARTIAL_ORDER();
    antlr4::tree::TerminalNode *OP_CONCURRENCY_PARALLEL();
    antlr4::tree::TerminalNode *OP_CONCURRENCY_RDV_ASYNC();
    antlr4::tree::TerminalNode *OP_CONCURRENCY_RDV_AND();
    antlr4::tree::TerminalNode *OP_CONCURRENCY_RDV_OR();
    antlr4::tree::TerminalNode *OP_CONCURRENCY_RDV_INTERLEAVING();
    antlr4::tree::TerminalNode *OP_CONCURRENCY_RDV_PARALLEL();

   
  };

  Op_concurrencyContext* op_concurrency();

  class  Op_invokableContext : public antlr4::ParserRuleContext {
  public:
    sep::Operator * op;
    Op_invokableContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *PLUS();
    antlr4::tree::TerminalNode *MINUS();
    antlr4::tree::TerminalNode *STAR();
    antlr4::tree::TerminalNode *DIV();
    antlr4::tree::TerminalNode *MOD();
    antlr4::tree::TerminalNode *EQUAL();
    antlr4::tree::TerminalNode *NEQUAL();
    antlr4::tree::TerminalNode *SEQUAL();
    antlr4::tree::TerminalNode *NSEQUAL();
    antlr4::tree::TerminalNode *GT();
    antlr4::tree::TerminalNode *GTE();
    antlr4::tree::TerminalNode *LT_();
    antlr4::tree::TerminalNode *LTE();
    antlr4::tree::TerminalNode *LNOT();
    antlr4::tree::TerminalNode *LAND();
    antlr4::tree::TerminalNode *LAND_THEN();
    antlr4::tree::TerminalNode *LOR();
    antlr4::tree::TerminalNode *LOR_ELSE();
    antlr4::tree::TerminalNode *BNOT();
    antlr4::tree::TerminalNode *BAND();
    antlr4::tree::TerminalNode *BOR();
    antlr4::tree::TerminalNode *BXOR();
    antlr4::tree::TerminalNode *LSHIFT();
    antlr4::tree::TerminalNode *RSHIFT();
    antlr4::tree::TerminalNode *ASSIGN();
    antlr4::tree::TerminalNode *ASSIGN_AFTER();
    antlr4::tree::TerminalNode *ASSIGN_REF();
    antlr4::tree::TerminalNode *ASSIGN_MACRO();
    antlr4::tree::TerminalNode *OP_PUSH();
    antlr4::tree::TerminalNode *OP_ASSIGN_TOP();
    antlr4::tree::TerminalNode *OP_TOP();
    antlr4::tree::TerminalNode *OP_POP();

   
  };

  Op_invokableContext* op_invokable();

  class  Prefix_statementContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    FMLParser::Avm_operatorContext *a = nullptr;
    FMLParser::Prefix_statementContext *ps = nullptr;
    FMLParser::UnaryExpressionContext *e = nullptr;
    Prefix_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *DOLLAR_LCURLY();
    antlr4::tree::TerminalNode *RCURLY();
    Avm_operatorContext *avm_operator();
    std::vector<Prefix_statementContext *> prefix_statement();
    Prefix_statementContext* prefix_statement(size_t i);
    std::vector<UnaryExpressionContext *> unaryExpression();
    UnaryExpressionContext* unaryExpression(size_t i);

   
  };

  Prefix_statementContext* prefix_statement();

  class  Prefix_expressionContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    FMLParser::Avm_operatorContext *a = nullptr;
    FMLParser::Prefix_expressionContext *ps = nullptr;
    FMLParser::UnaryExpressionContext *e = nullptr;
    Prefix_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *DOLLAR_LCURLY();
    antlr4::tree::TerminalNode *RCURLY();
    Avm_operatorContext *avm_operator();
    std::vector<Prefix_expressionContext *> prefix_expression();
    Prefix_expressionContext* prefix_expression(size_t i);
    std::vector<UnaryExpressionContext *> unaryExpression();
    UnaryExpressionContext* unaryExpression(size_t i);

   
  };

  Prefix_expressionContext* prefix_expression();

  class  Avm_operatorContext : public antlr4::ParserRuleContext {
  public:
    const sep::Operator * op;
    FMLParser::Op_invokableContext *oi = nullptr;
    FMLParser::Op_activityContext *oa = nullptr;
    Avm_operatorContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Op_invokableContext *op_invokable();
    Op_activityContext *op_activity();
    antlr4::tree::TerminalNode *ID();

   
  };

  Avm_operatorContext* avm_operator();

  class  Statement_invoke_methodContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    antlr4::Token *id = nullptr;
    Statement_invoke_methodContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *SEMI();
    antlr4::tree::TerminalNode *ID();
    Decl_instance_machine_paramsContext *decl_instance_machine_params();
    Decl_instance_machine_returnsContext *decl_instance_machine_returns();

   
  };

  Statement_invoke_methodContext* statement_invoke_method();

  class  Statement_invokeContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    FMLParser::UnaryExpressionContext *ue = nullptr;
    antlr4::Token *id = nullptr;
    FMLParser::Op_invokableContext *op = nullptr;
    FMLParser::ExpressionContext *e = nullptr;
    FMLParser::Op_activityContext *o = nullptr;
    Statement_invokeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LPAREN_INVOKE();
    antlr4::tree::TerminalNode *RPAREN();
    antlr4::tree::TerminalNode *SEMI();
    std::vector<UnaryExpressionContext *> unaryExpression();
    UnaryExpressionContext* unaryExpression(size_t i);
    antlr4::tree::TerminalNode *ID();
    Op_invokableContext *op_invokable();
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);
    Op_activityContext *op_activity();

   
  };

  Statement_invokeContext* statement_invoke();

  class  Expression_invokeContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    FMLParser::UnaryExpressionContext *ue = nullptr;
    antlr4::Token *id = nullptr;
    FMLParser::Op_invokableContext *oi = nullptr;
    FMLParser::ExpressionContext *e = nullptr;
    Expression_invokeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LPAREN_INVOKE();
    antlr4::tree::TerminalNode *RPAREN();
    UnaryExpressionContext *unaryExpression();
    antlr4::tree::TerminalNode *ID();
    Op_invokableContext *op_invokable();
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);

   
  };

  Expression_invokeContext* expression_invoke();

  class  Statement_activity_newContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    FMLParser::QualifiedNameIDContext *id = nullptr;
    FMLParser::ExpressionContext *e = nullptr;
    Statement_activity_newContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Decl_instance_dynamic_implContext *decl_instance_dynamic_impl();
    antlr4::tree::TerminalNode *SEMI();
    QualifiedNameIDContext *qualifiedNameID();
    ExpressionContext *expression();

   
  };

  Statement_activity_newContext* statement_activity_new();

  class  Decl_instance_dynamic_implContext : public antlr4::ParserRuleContext {
  public:
    sep::Machine * container;
    sep::Machine * ptrInstance;
    FMLParser::StatementContext *s = nullptr;
    Decl_instance_dynamic_implContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Decl_instance_dynamic_implContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Machine * container, sep::Machine * ptrInstance);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LPAREN();
    antlr4::tree::TerminalNode *RPAREN();
    antlr4::tree::TerminalNode *LCURLY();
    antlr4::tree::TerminalNode *RCURLY();
    Def_instance_on_new_activityContext *def_instance_on_new_activity();
    std::vector<Def_instance_activityContext *> def_instance_activity();
    Def_instance_activityContext* def_instance_activity(size_t i);
    std::vector<StatementContext *> statement();
    StatementContext* statement(size_t i);

   
  };

  Decl_instance_dynamic_implContext* decl_instance_dynamic_impl(sep::Machine * container,sep::Machine * ptrInstance);

  class  Expression_activity_newContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    FMLParser::QualifiedNameIDContext *id = nullptr;
    Expression_activity_newContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Activity_machine_param_returnContext *activity_machine_param_return();
    QualifiedNameIDContext *qualifiedNameID();

   
  };

  Expression_activity_newContext* expression_activity_new();

  class  Statement_promptContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    FMLParser::Statement_prompt_obsContext *spi = nullptr;
    Statement_promptContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Statement_prompt_obsContext *statement_prompt_obs();

   
  };

  Statement_promptContext* statement_prompt();

  class  Statement_prompt_obsContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    FMLParser::QualifiedNameIDContext *id = nullptr;
    FMLParser::Statement_prompt_obs_comContext *bs = nullptr;
    FMLParser::ExpressionContext *e = nullptr;
    Statement_prompt_obsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LCURLY();
    antlr4::tree::TerminalNode *RCURLY();
    Statement_prompt_obs_comContext *statement_prompt_obs_com();
    antlr4::tree::TerminalNode *LPAREN();
    antlr4::tree::TerminalNode *RPAREN();
    antlr4::tree::TerminalNode *SEMI();
    QualifiedNameIDContext *qualifiedNameID();
    antlr4::tree::TerminalNode *LBRACKET();
    antlr4::tree::TerminalNode *RBRACKET();
    ExpressionContext *expression();

   
  };

  Statement_prompt_obsContext* statement_prompt_obs();

  class  Statement_prompt_obs_comContext : public antlr4::ParserRuleContext {
  public:
    sep::BF varMachine;
    sep::BFCode ac;
    FMLParser::Statement_comContext *sc = nullptr;
    Statement_prompt_obs_comContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Statement_prompt_obs_comContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::BF varMachine);
    virtual size_t getRuleIndex() const override;
    Statement_comContext *statement_com();

   
  };

  Statement_prompt_obs_comContext* statement_prompt_obs_com(sep::BF varMachine);

  class  Meta_statementContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    FMLParser::StatementContext *s = nullptr;
    FMLParser::ExpressionContext *e = nullptr;
    Meta_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LCURLY();
    antlr4::tree::TerminalNode *RCURLY();
    std::vector<StatementContext *> statement();
    StatementContext* statement(size_t i);
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);

   
  };

  Meta_statementContext* meta_statement();

  class  Statement_assignContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    FMLParser::LvalueContext *lv = nullptr;
    FMLParser::ExpressionContext *e = nullptr;
    FMLParser::LvalueContext *rlv = nullptr;
    FMLParser::LvalueContext *v = nullptr;
    Statement_assignContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<LvalueContext *> lvalue();
    LvalueContext* lvalue(size_t i);
    antlr4::tree::TerminalNode *SEMI();
    antlr4::tree::TerminalNode *ASSIGN_REF();
    antlr4::tree::TerminalNode *ASSIGN_MACRO();
    std::vector<antlr4::tree::TerminalNode *> OP_PUSH();
    antlr4::tree::TerminalNode* OP_PUSH(size_t i);
    antlr4::tree::TerminalNode *OP_ASSIGN_TOP();
    antlr4::tree::TerminalNode *OP_TOP();
    antlr4::tree::TerminalNode *OP_POP();
    antlr4::tree::TerminalNode *INCR();
    antlr4::tree::TerminalNode *DECR();
    antlr4::tree::TerminalNode *ASSIGN();
    antlr4::tree::TerminalNode *ASSIGN_AFTER();
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);
    antlr4::tree::TerminalNode *PLUS_ASSIGN();
    antlr4::tree::TerminalNode *PLUS_ASSIGN_AFTER();
    antlr4::tree::TerminalNode *MINUS_ASSIGN();
    antlr4::tree::TerminalNode *MINUS_ASSIGN_AFTER();
    antlr4::tree::TerminalNode *STAR_ASSIGN();
    antlr4::tree::TerminalNode *STAR_ASSIGN_AFTER();
    antlr4::tree::TerminalNode *DIV_ASSIGN();
    antlr4::tree::TerminalNode *DIV_ASSIGN_AFTER();
    antlr4::tree::TerminalNode *MOD_ASSIGN();
    antlr4::tree::TerminalNode *MOD_ASSIGN_AFTER();
    antlr4::tree::TerminalNode *LAND_ASSIGN();
    antlr4::tree::TerminalNode *LAND_ASSIGN_AFTER();
    antlr4::tree::TerminalNode *LOR_ASSIGN();
    antlr4::tree::TerminalNode *LOR_ASSIGN_AFTER();
    antlr4::tree::TerminalNode *BAND_ASSIGN();
    antlr4::tree::TerminalNode *BAND_ASSIGN_AFTER();
    antlr4::tree::TerminalNode *BOR_ASSIGN();
    antlr4::tree::TerminalNode *BOR_ASSIGN_AFTER();
    antlr4::tree::TerminalNode *BXOR_ASSIGN();
    antlr4::tree::TerminalNode *BXOR_ASSIGN_AFTER();
    antlr4::tree::TerminalNode *LSHIFT_ASSIGN();
    antlr4::tree::TerminalNode *LSHIFT_ASSIGN_AFTER();
    antlr4::tree::TerminalNode *RSHIFT_ASSIGN();
    antlr4::tree::TerminalNode *RSHIFT_ASSIGN_AFTER();

   
  };

  Statement_assignContext* statement_assign();

  class  LvalueContext : public antlr4::ParserRuleContext {
  public:
    sep::BF bf;
    antlr4::Token *id = nullptr;
    FMLParser::ExpressionContext *e = nullptr;
    LvalueContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<antlr4::tree::TerminalNode *> ID();
    antlr4::tree::TerminalNode* ID(size_t i);
    antlr4::tree::TerminalNode *COLONx2();
    std::vector<antlr4::tree::TerminalNode *> DOT();
    antlr4::tree::TerminalNode* DOT(size_t i);
    std::vector<antlr4::tree::TerminalNode *> LBRACKET();
    antlr4::tree::TerminalNode* LBRACKET(size_t i);
    std::vector<antlr4::tree::TerminalNode *> RBRACKET();
    antlr4::tree::TerminalNode* RBRACKET(size_t i);
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);

   
  };

  LvalueContext* lvalue();

  class  ParametersContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    FMLParser::ExpressionContext *e = nullptr;
    ParametersContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    ParametersContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::BFCode ac);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LPAREN();
    antlr4::tree::TerminalNode *RPAREN();
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

   
  };

  ParametersContext* parameters(sep::BFCode ac);

  class  Statement_comContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    FMLParser::Statement_com_inputContext *si = nullptr;
    FMLParser::Statement_com_outputContext *so = nullptr;
    Statement_comContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Statement_com_inputContext *statement_com_input();
    Statement_com_outputContext *statement_com_output();

   
  };

  Statement_comContext* statement_com();

  class  Statement_com_inputContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    antlr4::Token *tok = nullptr;
    FMLParser::QualifiedNameIDContext *id = nullptr;
    FMLParser::ExpressionContext *me = nullptr;
    Statement_com_inputContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *SEMI();
    std::vector<QualifiedNameIDContext *> qualifiedNameID();
    QualifiedNameIDContext* qualifiedNameID(size_t i);
    Parameters_portContext *parameters_port();
    ExpressionContext *expression();
    antlr4::tree::TerminalNode *ASSIGN_REF();

   
  };

  Statement_com_inputContext* statement_com_input();

  class  Statement_com_outputContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    antlr4::Token *tok = nullptr;
    FMLParser::QualifiedNameIDContext *id = nullptr;
    FMLParser::ExpressionContext *me = nullptr;
    Statement_com_outputContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *SEMI();
    std::vector<QualifiedNameIDContext *> qualifiedNameID();
    QualifiedNameIDContext* qualifiedNameID(size_t i);
    Parameters_portContext *parameters_port();
    ExpressionContext *expression();

   
  };

  Statement_com_outputContext* statement_com_output();

  class  Parameters_portContext : public antlr4::ParserRuleContext {
  public:
    sep::Port * port;
    sep::BFCode ac;
    FMLParser::Labelled_argumentContext *lp = nullptr;
    Parameters_portContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Parameters_portContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Port * port, sep::BFCode ac);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LPAREN();
    antlr4::tree::TerminalNode *RPAREN();
    std::vector<Labelled_argumentContext *> labelled_argument();
    Labelled_argumentContext* labelled_argument(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

   
  };

  Parameters_portContext* parameters_port(sep::Port * port,sep::BFCode ac);

  class  Expression_comContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    FMLParser::QualifiedNameIDContext *id = nullptr;
    Expression_comContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    QualifiedNameIDContext *qualifiedNameID();

   
  };

  Expression_comContext* expression_com();

  class  Statement_constraintContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    FMLParser::Statement_guardContext *sg = nullptr;
    FMLParser::Statement_timed_guardContext *st = nullptr;
    FMLParser::Statement_checksatContext *sc = nullptr;
    Statement_constraintContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Statement_guardContext *statement_guard();
    Statement_timed_guardContext *statement_timed_guard();
    Statement_checksatContext *statement_checksat();

   
  };

  Statement_constraintContext* statement_constraint();

  class  Statement_guardContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    FMLParser::ExpressionContext *e = nullptr;
    Statement_guardContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *SEMI();
    ExpressionContext *expression();

   
  };

  Statement_guardContext* statement_guard();

  class  Statement_timed_guardContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    FMLParser::ExpressionContext *e = nullptr;
    Statement_timed_guardContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *SEMI();
    ExpressionContext *expression();

   
  };

  Statement_timed_guardContext* statement_timed_guard();

  class  Statement_checksatContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    antlr4::Token *id = nullptr;
    FMLParser::ExpressionContext *e = nullptr;
    Statement_checksatContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *SEMI();
    ExpressionContext *expression();
    antlr4::tree::TerminalNode *LT_();
    antlr4::tree::TerminalNode *GT();
    antlr4::tree::TerminalNode *StringLiteral();
    antlr4::tree::TerminalNode *ID();

   
  };

  Statement_checksatContext* statement_checksat();

  class  Expression_checksatContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    antlr4::Token *id = nullptr;
    FMLParser::ExpressionContext *e = nullptr;
    Expression_checksatContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    ExpressionContext *expression();
    antlr4::tree::TerminalNode *LT_();
    antlr4::tree::TerminalNode *GT();
    antlr4::tree::TerminalNode *StringLiteral();
    antlr4::tree::TerminalNode *ID();

   
  };

  Expression_checksatContext* expression_checksat();

  class  Expression_quantifierContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    antlr4::Token *id = nullptr;
    FMLParser::Type_varContext *tv = nullptr;
    FMLParser::ExpressionContext *e = nullptr;
    Expression_quantifierContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LT_();
    antlr4::tree::TerminalNode *GT();
    ExpressionContext *expression();
    std::vector<antlr4::tree::TerminalNode *> COLON();
    antlr4::tree::TerminalNode* COLON(size_t i);
    std::vector<antlr4::tree::TerminalNode *> ID();
    antlr4::tree::TerminalNode* ID(size_t i);
    std::vector<Type_varContext *> type_var();
    Type_varContext* type_var(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

   
  };

  Expression_quantifierContext* expression_quantifier();

  class  Statement_iteContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    FMLParser::ExpressionContext *e = nullptr;
    FMLParser::Block_statementContext *bs = nullptr;
    Statement_iteContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);
    std::vector<Block_statementContext *> block_statement();
    Block_statementContext* block_statement(size_t i);

   
  };

  Statement_iteContext* statement_ite();

  class  Expression_iteContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    FMLParser::ExpressionContext *c = nullptr;
    FMLParser::ExpressionContext *e = nullptr;
    Expression_iteContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<antlr4::tree::TerminalNode *> LCURLY();
    antlr4::tree::TerminalNode* LCURLY(size_t i);
    std::vector<antlr4::tree::TerminalNode *> RCURLY();
    antlr4::tree::TerminalNode* RCURLY(size_t i);
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);

   
  };

  Expression_iteContext* expression_ite();

  class  Statement_iterationContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    FMLParser::For_assign_headerContext *isa = nullptr;
    FMLParser::ExpressionContext *e = nullptr;
    FMLParser::For_assign_headerContext *sai = nullptr;
    FMLParser::LvalueContext *lv = nullptr;
    FMLParser::Block_statementContext *sa = nullptr;
    FMLParser::Block_statementContext *bs = nullptr;
    Statement_iterationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Block_statementContext *block_statement();
    std::vector<antlr4::tree::TerminalNode *> SEMI();
    antlr4::tree::TerminalNode* SEMI(size_t i);
    antlr4::tree::TerminalNode *LPAREN();
    antlr4::tree::TerminalNode *RPAREN();
    antlr4::tree::TerminalNode *COLON();
    std::vector<For_assign_headerContext *> for_assign_header();
    For_assign_headerContext* for_assign_header(size_t i);
    ExpressionContext *expression();
    LvalueContext *lvalue();

   
  };

  Statement_iterationContext* statement_iteration();

  class  For_assign_headerContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    FMLParser::LvalueContext *lv = nullptr;
    FMLParser::ExpressionContext *e = nullptr;
    For_assign_headerContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    LvalueContext *lvalue();
    antlr4::tree::TerminalNode *ASSIGN();
    antlr4::tree::TerminalNode *INCR();
    antlr4::tree::TerminalNode *DECR();
    ExpressionContext *expression();

   
  };

  For_assign_headerContext* for_assign_header();

  class  Statement_jumpContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    FMLParser::ExpressionContext *e = nullptr;
    Statement_jumpContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *SEMI();
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

   
  };

  Statement_jumpContext* statement_jump();

  class  Expression_lambdaContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    antlr4::Token *id = nullptr;
    FMLParser::ExpressionContext *e = nullptr;
    Expression_lambdaContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    ExpressionContext *expression();
    std::vector<antlr4::tree::TerminalNode *> ID();
    antlr4::tree::TerminalNode* ID(size_t i);

   
  };

  Expression_lambdaContext* expression_lambda();

  class  Expression_statusContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    FMLParser::Op_activityContext *o = nullptr;
    FMLParser::QualifiedNameIDContext *id = nullptr;
    FMLParser::LvalueContext *lv = nullptr;
    Expression_statusContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Op_activityContext *op_activity();
    QualifiedNameIDContext *qualifiedNameID();
    LvalueContext *lvalue();

   
  };

  Expression_statusContext* expression_status();

  class  Op_activityContext : public antlr4::ParserRuleContext {
  public:
    sep::Operator * op;
    Op_activityContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;

   
  };

  Op_activityContext* op_activity();

  class  Statement_activityContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    FMLParser::Op_activityContext *o = nullptr;
    FMLParser::QualifiedNameIDContext *id = nullptr;
    FMLParser::ExpressionContext *e = nullptr;
    FMLParser::Statement_init_flowContext *fs = nullptr;
    Statement_activityContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *SEMI();
    Op_activityContext *op_activity();
    Activity_machine_param_returnContext *activity_machine_param_return();
    QualifiedNameIDContext *qualifiedNameID();
    antlr4::tree::TerminalNode *LPAREN();
    antlr4::tree::TerminalNode *RPAREN();
    antlr4::tree::TerminalNode *LT_();
    antlr4::tree::TerminalNode *GT();
    ExpressionContext *expression();
    Statement_init_flowContext *statement_init_flow();

   
  };

  Statement_activityContext* statement_activity();

  class  Statement_init_flowContext : public antlr4::ParserRuleContext {
  public:
    sep::BF flowTarget;
    sep::BFCode ac;
    FMLParser::Block_statementContext *bs = nullptr;
    Statement_init_flowContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Statement_init_flowContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::BF flowTarget);
    virtual size_t getRuleIndex() const override;
    Block_statementContext *block_statement();

   
  };

  Statement_init_flowContext* statement_init_flow(sep::BF flowTarget);

  class  Statement_invoke_routineContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    antlr4::Token *id = nullptr;
    Statement_invoke_routineContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Invoke_routine_paramsContext *invoke_routine_params();
    antlr4::tree::TerminalNode *SEMI();
    antlr4::tree::TerminalNode *ID();
    Invoke_routine_returnsContext *invoke_routine_returns();

   
  };

  Statement_invoke_routineContext* statement_invoke_routine();

  class  Invoke_routine_paramsContext : public antlr4::ParserRuleContext {
  public:
    sep::Routine * invokeRoutine;
    FMLParser::Labelled_argumentContext *lp = nullptr;
    Invoke_routine_paramsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Invoke_routine_paramsContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Routine * invokeRoutine);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LPAREN();
    antlr4::tree::TerminalNode *RPAREN();
    std::vector<Labelled_argumentContext *> labelled_argument();
    Labelled_argumentContext* labelled_argument(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

   
  };

  Invoke_routine_paramsContext* invoke_routine_params(sep::Routine * invokeRoutine);

  class  Invoke_routine_returnsContext : public antlr4::ParserRuleContext {
  public:
    sep::Routine * invokeRoutine;
    FMLParser::Labelled_argumentContext *lp = nullptr;
    Invoke_routine_returnsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Invoke_routine_returnsContext(antlr4::ParserRuleContext *parent, size_t invokingState, sep::Routine * invokeRoutine);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LPAREN();
    antlr4::tree::TerminalNode *RPAREN();
    std::vector<Labelled_argumentContext *> labelled_argument();
    Labelled_argumentContext* labelled_argument(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

   
  };

  Invoke_routine_returnsContext* invoke_routine_returns(sep::Routine * invokeRoutine);

  class  Statement_mocContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    antlr4::Token *stringliteralToken = nullptr;
    Statement_mocContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *StringLiteral();
    antlr4::tree::TerminalNode *SEMI();

   
  };

  Statement_mocContext* statement_moc();

  class  ExpressionContext : public antlr4::ParserRuleContext {
  public:
    sep::BF bf;
    FMLParser::ConditionalExpressionContext *ce = nullptr;
    FMLParser::ExpressionContext *e = nullptr;
    ExpressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    ConditionalExpressionContext *conditionalExpression();
    antlr4::tree::TerminalNode *ASSIGN();
    antlr4::tree::TerminalNode *ASSIGN_MACRO();
    antlr4::tree::TerminalNode *ASSIGN_AFTER();
    antlr4::tree::TerminalNode *PLUS_ASSIGN();
    antlr4::tree::TerminalNode *PLUS_ASSIGN_AFTER();
    antlr4::tree::TerminalNode *MINUS_ASSIGN();
    antlr4::tree::TerminalNode *MINUS_ASSIGN_AFTER();
    antlr4::tree::TerminalNode *STAR_ASSIGN();
    antlr4::tree::TerminalNode *STAR_ASSIGN_AFTER();
    antlr4::tree::TerminalNode *DIV_ASSIGN();
    antlr4::tree::TerminalNode *DIV_ASSIGN_AFTER();
    antlr4::tree::TerminalNode *MOD_ASSIGN();
    antlr4::tree::TerminalNode *MOD_ASSIGN_AFTER();
    antlr4::tree::TerminalNode *LAND_ASSIGN();
    antlr4::tree::TerminalNode *LAND_ASSIGN_AFTER();
    antlr4::tree::TerminalNode *LOR_ASSIGN();
    antlr4::tree::TerminalNode *LOR_ASSIGN_AFTER();
    antlr4::tree::TerminalNode *BAND_ASSIGN();
    antlr4::tree::TerminalNode *BAND_ASSIGN_AFTER();
    antlr4::tree::TerminalNode *BOR_ASSIGN();
    antlr4::tree::TerminalNode *BOR_ASSIGN_AFTER();
    antlr4::tree::TerminalNode *BXOR_ASSIGN();
    antlr4::tree::TerminalNode *BXOR_ASSIGN_AFTER();
    antlr4::tree::TerminalNode *LSHIFT_ASSIGN();
    antlr4::tree::TerminalNode *LSHIFT_ASSIGN_AFTER();
    antlr4::tree::TerminalNode *RSHIFT_ASSIGN();
    antlr4::tree::TerminalNode *RSHIFT_ASSIGN_AFTER();
    antlr4::tree::TerminalNode *OP_PUSH();
    antlr4::tree::TerminalNode *OP_ASSIGN_TOP();
    antlr4::tree::TerminalNode *OP_POP();
    ExpressionContext *expression();

   
  };

  ExpressionContext* expression();

  class  ConditionalExpressionContext : public antlr4::ParserRuleContext {
  public:
    sep::BF bf;
    FMLParser::ScheduleExpressionContext *e = nullptr;
    FMLParser::ExpressionContext *th = nullptr;
    FMLParser::ExpressionContext *el = nullptr;
    ConditionalExpressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    ScheduleExpressionContext *scheduleExpression();
    antlr4::tree::TerminalNode *QUESTION();
    antlr4::tree::TerminalNode *COLON();
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);

   
  };

  ConditionalExpressionContext* conditionalExpression();

  class  ScheduleExpressionContext : public antlr4::ParserRuleContext {
  public:
    sep::BF bf;
    FMLParser::ConditionalOrExpressionContext *e = nullptr;
    FMLParser::Op_sequenceContext *os = nullptr;
    FMLParser::Op_schedulingContext *oh = nullptr;
    FMLParser::Op_concurrencyContext *oc = nullptr;
    ScheduleExpressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<ConditionalOrExpressionContext *> conditionalOrExpression();
    ConditionalOrExpressionContext* conditionalOrExpression(size_t i);
    std::vector<Op_sequenceContext *> op_sequence();
    Op_sequenceContext* op_sequence(size_t i);
    std::vector<Op_schedulingContext *> op_scheduling();
    Op_schedulingContext* op_scheduling(size_t i);
    std::vector<Op_concurrencyContext *> op_concurrency();
    Op_concurrencyContext* op_concurrency(size_t i);

   
  };

  ScheduleExpressionContext* scheduleExpression();

  class  ConditionalOrExpressionContext : public antlr4::ParserRuleContext {
  public:
    sep::BF bf;
    FMLParser::ConditionalImpliesExpressionContext *e = nullptr;
    ConditionalOrExpressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<ConditionalImpliesExpressionContext *> conditionalImpliesExpression();
    ConditionalImpliesExpressionContext* conditionalImpliesExpression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> LOR();
    antlr4::tree::TerminalNode* LOR(size_t i);

   
  };

  ConditionalOrExpressionContext* conditionalOrExpression();

  class  ConditionalImpliesExpressionContext : public antlr4::ParserRuleContext {
  public:
    sep::BF bf;
    FMLParser::ConditionalAndExpressionContext *e = nullptr;
    ConditionalImpliesExpressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<ConditionalAndExpressionContext *> conditionalAndExpression();
    ConditionalAndExpressionContext* conditionalAndExpression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> LIMPLIES();
    antlr4::tree::TerminalNode* LIMPLIES(size_t i);

   
  };

  ConditionalImpliesExpressionContext* conditionalImpliesExpression();

  class  ConditionalAndExpressionContext : public antlr4::ParserRuleContext {
  public:
    sep::BF bf;
    FMLParser::BitwiseOrExpressionContext *e = nullptr;
    ConditionalAndExpressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<BitwiseOrExpressionContext *> bitwiseOrExpression();
    BitwiseOrExpressionContext* bitwiseOrExpression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> LAND();
    antlr4::tree::TerminalNode* LAND(size_t i);

   
  };

  ConditionalAndExpressionContext* conditionalAndExpression();

  class  BitwiseOrExpressionContext : public antlr4::ParserRuleContext {
  public:
    sep::BF bf;
    FMLParser::BitwiseXorExpressionContext *e = nullptr;
    BitwiseOrExpressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<BitwiseXorExpressionContext *> bitwiseXorExpression();
    BitwiseXorExpressionContext* bitwiseXorExpression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> BOR();
    antlr4::tree::TerminalNode* BOR(size_t i);

   
  };

  BitwiseOrExpressionContext* bitwiseOrExpression();

  class  BitwiseXorExpressionContext : public antlr4::ParserRuleContext {
  public:
    sep::BF bf;
    FMLParser::BitwiseAndExpressionContext *e = nullptr;
    BitwiseXorExpressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<BitwiseAndExpressionContext *> bitwiseAndExpression();
    BitwiseAndExpressionContext* bitwiseAndExpression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> BXOR();
    antlr4::tree::TerminalNode* BXOR(size_t i);

   
  };

  BitwiseXorExpressionContext* bitwiseXorExpression();

  class  BitwiseAndExpressionContext : public antlr4::ParserRuleContext {
  public:
    sep::BF bf;
    FMLParser::EqualityExpressionContext *e = nullptr;
    BitwiseAndExpressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<EqualityExpressionContext *> equalityExpression();
    EqualityExpressionContext* equalityExpression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> BAND();
    antlr4::tree::TerminalNode* BAND(size_t i);

   
  };

  BitwiseAndExpressionContext* bitwiseAndExpression();

  class  EqualityExpressionContext : public antlr4::ParserRuleContext {
  public:
    sep::BF bf;
    FMLParser::RelationalExpressionContext *e = nullptr;
    FMLParser::EqualOpContext *eq = nullptr;
    EqualityExpressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<RelationalExpressionContext *> relationalExpression();
    RelationalExpressionContext* relationalExpression(size_t i);
    std::vector<EqualOpContext *> equalOp();
    EqualOpContext* equalOp(size_t i);

   
  };

  EqualityExpressionContext* equalityExpression();

  class  EqualOpContext : public antlr4::ParserRuleContext {
  public:
    const sep::Operator * op;
    EqualOpContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *EQUAL();
    antlr4::tree::TerminalNode *NEQUAL();
    antlr4::tree::TerminalNode *SEQUAL();
    antlr4::tree::TerminalNode *NSEQUAL();

   
  };

  EqualOpContext* equalOp();

  class  RelationalExpressionContext : public antlr4::ParserRuleContext {
  public:
    sep::BF bf;
    FMLParser::ShiftExpressionContext *e = nullptr;
    FMLParser::RelationalOpContext *r = nullptr;
    RelationalExpressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<ShiftExpressionContext *> shiftExpression();
    ShiftExpressionContext* shiftExpression(size_t i);
    std::vector<RelationalOpContext *> relationalOp();
    RelationalOpContext* relationalOp(size_t i);

   
  };

  RelationalExpressionContext* relationalExpression();

  class  RelationalOpContext : public antlr4::ParserRuleContext {
  public:
    const sep::Operator * op;
    RelationalOpContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LTE();
    antlr4::tree::TerminalNode *GTE();
    antlr4::tree::TerminalNode *LT_();
    antlr4::tree::TerminalNode *GT();

   
  };

  RelationalOpContext* relationalOp();

  class  ShiftExpressionContext : public antlr4::ParserRuleContext {
  public:
    sep::BF bf;
    FMLParser::AdditiveExpressionContext *e = nullptr;
    FMLParser::ShiftOpContext *s = nullptr;
    ShiftExpressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<AdditiveExpressionContext *> additiveExpression();
    AdditiveExpressionContext* additiveExpression(size_t i);
    std::vector<ShiftOpContext *> shiftOp();
    ShiftOpContext* shiftOp(size_t i);

   
  };

  ShiftExpressionContext* shiftExpression();

  class  ShiftOpContext : public antlr4::ParserRuleContext {
  public:
    const sep::Operator * op;
    ShiftOpContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LSHIFT();
    antlr4::tree::TerminalNode *RSHIFT();

   
  };

  ShiftOpContext* shiftOp();

  class  AdditiveExpressionContext : public antlr4::ParserRuleContext {
  public:
    sep::BF bf;
    FMLParser::MultiplicativeExpressionContext *e = nullptr;
    AdditiveExpressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<MultiplicativeExpressionContext *> multiplicativeExpression();
    MultiplicativeExpressionContext* multiplicativeExpression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> PLUS();
    antlr4::tree::TerminalNode* PLUS(size_t i);
    std::vector<antlr4::tree::TerminalNode *> MINUS();
    antlr4::tree::TerminalNode* MINUS(size_t i);

   
  };

  AdditiveExpressionContext* additiveExpression();

  class  MultiplicativeExpressionContext : public antlr4::ParserRuleContext {
  public:
    sep::BF bf;
    FMLParser::UnaryExpressionContext *e = nullptr;
    MultiplicativeExpressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<UnaryExpressionContext *> unaryExpression();
    UnaryExpressionContext* unaryExpression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> STAR();
    antlr4::tree::TerminalNode* STAR(size_t i);
    std::vector<antlr4::tree::TerminalNode *> DIV();
    antlr4::tree::TerminalNode* DIV(size_t i);
    std::vector<antlr4::tree::TerminalNode *> MOD();
    antlr4::tree::TerminalNode* MOD(size_t i);

   
  };

  MultiplicativeExpressionContext* multiplicativeExpression();

  class  UnaryExpressionContext : public antlr4::ParserRuleContext {
  public:
    sep::BF bf;
    FMLParser::UnaryExpressionContext *e = nullptr;
    FMLParser::Prefix_expressionContext *pe = nullptr;
    FMLParser::Expression_invokeContext *ei = nullptr;
    FMLParser::Expression_activity_newContext *ea = nullptr;
    FMLParser::Expression_comContext *ec = nullptr;
    FMLParser::Expression_checksatContext *ek = nullptr;
    FMLParser::Expression_quantifierContext *eq = nullptr;
    FMLParser::Expression_iteContext *et = nullptr;
    FMLParser::Expression_lambdaContext *el = nullptr;
    FMLParser::CtorExpressionContext *ce = nullptr;
    FMLParser::PrimaryContext *p = nullptr;
    FMLParser::LiteralContext *l = nullptr;
    FMLParser::Quote_expressionContext *qe = nullptr;
    FMLParser::Meta_eval_expressionContext *me = nullptr;
    FMLParser::ExpressionContext *le = nullptr;
    FMLParser::Collection_of_expressionContext *co = nullptr;
    UnaryExpressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *PLUS();
    UnaryExpressionContext *unaryExpression();
    antlr4::tree::TerminalNode *MINUS();
    antlr4::tree::TerminalNode *INCR();
    antlr4::tree::TerminalNode *DECR();
    antlr4::tree::TerminalNode *LNOT();
    antlr4::tree::TerminalNode *BNOT();
    antlr4::tree::TerminalNode *OP_POP();
    antlr4::tree::TerminalNode *OP_TOP();
    Prefix_expressionContext *prefix_expression();
    Expression_invokeContext *expression_invoke();
    Expression_activity_newContext *expression_activity_new();
    Expression_comContext *expression_com();
    Expression_checksatContext *expression_checksat();
    Expression_quantifierContext *expression_quantifier();
    Expression_iteContext *expression_ite();
    Expression_lambdaContext *expression_lambda();
    CtorExpressionContext *ctorExpression();
    PrimaryContext *primary();
    LiteralContext *literal();
    Quote_expressionContext *quote_expression();
    Meta_eval_expressionContext *meta_eval_expression();
    antlr4::tree::TerminalNode *LPAREN();
    antlr4::tree::TerminalNode *RPAREN();
    ExpressionContext *expression();
    Collection_of_expressionContext *collection_of_expression();

   
  };

  UnaryExpressionContext* unaryExpression();

  class  CtorExpressionContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ctor;
    FMLParser::Type_varContext *tv = nullptr;
    FMLParser::ExpressionContext *e = nullptr;
    CtorExpressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LT_();
    antlr4::tree::TerminalNode *GT();
    antlr4::tree::TerminalNode *LPAREN();
    antlr4::tree::TerminalNode *RPAREN();
    Type_varContext *type_var();
    ExpressionContext *expression();

   
  };

  CtorExpressionContext* ctorExpression();

  class  Quote_expressionContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    FMLParser::ExpressionContext *e = nullptr;
    Quote_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *PERCENT_LCURLY();
    antlr4::tree::TerminalNode *RCURLY_PERCENT();
    ExpressionContext *expression();

   
  };

  Quote_expressionContext* quote_expression();

  class  Meta_eval_expressionContext : public antlr4::ParserRuleContext {
  public:
    sep::BFCode ac;
    FMLParser::ExpressionContext *e = nullptr;
    Meta_eval_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LBRACKET_BAR();
    antlr4::tree::TerminalNode *BAR_RBRACKET();
    ExpressionContext *expression();

   
  };

  Meta_eval_expressionContext* meta_eval_expression();

  class  PrimaryContext : public antlr4::ParserRuleContext {
  public:
    sep::BF bf;
    antlr4::Token *id = nullptr;
    FMLParser::Primary_invokeContext *pi = nullptr;
    FMLParser::Primary_ufidContext *pu = nullptr;
    FMLParser::Primary_ufiContext *p = nullptr;
    PrimaryContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ID();
    Primary_invokeContext *primary_invoke();
    Primary_ufidContext *primary_ufid();
    Primary_ufiContext *primary_ufi();

   
  };

  PrimaryContext* primary();

  class  Primary_ufidContext : public antlr4::ParserRuleContext {
  public:
    std::string mainId;
    sep::BF bf;
    antlr4::Token *id = nullptr;
    FMLParser::ExpressionContext *e = nullptr;
    Primary_ufidContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Primary_ufidContext(antlr4::ParserRuleContext *parent, size_t invokingState, std::string mainId);
    virtual size_t getRuleIndex() const override;
    std::vector<antlr4::tree::TerminalNode *> DOT();
    antlr4::tree::TerminalNode* DOT(size_t i);
    std::vector<antlr4::tree::TerminalNode *> LBRACKET();
    antlr4::tree::TerminalNode* LBRACKET(size_t i);
    std::vector<antlr4::tree::TerminalNode *> RBRACKET();
    antlr4::tree::TerminalNode* RBRACKET(size_t i);
    std::vector<antlr4::tree::TerminalNode *> ID();
    antlr4::tree::TerminalNode* ID(size_t i);
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);

   
  };

  Primary_ufidContext* primary_ufid(std::string mainId);

  class  Primary_ufiContext : public antlr4::ParserRuleContext {
  public:
    std::string locatorId;
    sep::BF bf;
    antlr4::Token *id = nullptr;
    FMLParser::ExpressionContext *e = nullptr;
    Primary_ufiContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Primary_ufiContext(antlr4::ParserRuleContext *parent, size_t invokingState, std::string locatorId);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *COLONx2();
    std::vector<antlr4::tree::TerminalNode *> ID();
    antlr4::tree::TerminalNode* ID(size_t i);
    std::vector<antlr4::tree::TerminalNode *> DOT();
    antlr4::tree::TerminalNode* DOT(size_t i);
    std::vector<antlr4::tree::TerminalNode *> LBRACKET();
    antlr4::tree::TerminalNode* LBRACKET(size_t i);
    std::vector<antlr4::tree::TerminalNode *> RBRACKET();
    antlr4::tree::TerminalNode* RBRACKET(size_t i);
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);

   
  };

  Primary_ufiContext* primary_ufi(std::string locatorId);

  class  Primary_invokeContext : public antlr4::ParserRuleContext {
  public:
    std::string mainId;
    sep::BF bf;
    FMLParser::Labelled_argumentContext *lp = nullptr;
    Primary_invokeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Primary_invokeContext(antlr4::ParserRuleContext *parent, size_t invokingState, std::string mainId);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LPAREN();
    antlr4::tree::TerminalNode *RPAREN();
    std::vector<Labelled_argumentContext *> labelled_argument();
    Labelled_argumentContext* labelled_argument(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

   
  };

  Primary_invokeContext* primary_invoke(std::string mainId);

  class  LiteralContext : public antlr4::ParserRuleContext {
  public:
    sep::BF bf;
    antlr4::Token *integerliteralToken = nullptr;
    antlr4::Token *rationalliteralToken = nullptr;
    antlr4::Token *floatliteralToken = nullptr;
    antlr4::Token *charliteralToken = nullptr;
    antlr4::Token *stringliteralToken = nullptr;
    FMLParser::QualifiedNameIDContext *id = nullptr;
    LiteralContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *IntegerLiteral();
    antlr4::tree::TerminalNode *RationalLiteral();
    antlr4::tree::TerminalNode *FloatLiteral();
    antlr4::tree::TerminalNode *CharLiteral();
    antlr4::tree::TerminalNode *StringLiteral();
    antlr4::tree::TerminalNode *LPAREN();
    antlr4::tree::TerminalNode *RPAREN();
    antlr4::tree::TerminalNode *LT_();
    antlr4::tree::TerminalNode *GT();
    QualifiedNameIDContext *qualifiedNameID();

   
  };

  LiteralContext* literal();

  class  Collection_of_expressionContext : public antlr4::ParserRuleContext {
  public:
    sep::BF bf;
    FMLParser::ExpressionContext *e = nullptr;
    Collection_of_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LCURLY();
    antlr4::tree::TerminalNode *RCURLY();
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    antlr4::tree::TerminalNode *LBRACKET();
    antlr4::tree::TerminalNode *RBRACKET();

   
  };

  Collection_of_expressionContext* collection_of_expression();


  bool sempred(antlr4::RuleContext *_localctx, size_t ruleIndex, size_t predicateIndex) override;

  bool avm_operatorSempred(Avm_operatorContext *_localctx, size_t predicateIndex);

  // By default the static state used to implement the parser is lazily initialized during the first
  // call to the constructor. You can call this function if you wish to initialize the static state
  // ahead of time.
  static void initialize();

private:
  /* private parser declarations section */
  	
  	std::string mFilename;
  	
  	std::size_t   noOfErrors;


};

}  // namespace sep
