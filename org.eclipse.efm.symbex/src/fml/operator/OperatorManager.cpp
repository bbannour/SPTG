/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 15 août 2008
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "OperatorManager.h"

#include <fml/expression/AvmCode.h>

#include <fml/operator/Operator.h>


namespace sep
{


std::map< std::string , Operator * > OperatorManager::theOperatorsMap;

BFVector OperatorManager::TABLE_OF_OPERATOR;



/*
 *******************************************************************************
 * AVM NULL / NOP STATEMENT
 *******************************************************************************
 */
Operator * OperatorManager::OPERATOR_NULL = nullptr;

Operator * OperatorManager::OPERATOR_NOP  = nullptr;


/*
 *******************************************************************************
 * AVM META STATEMENT
 *******************************************************************************
 */
Operator * OperatorManager::OPERATOR_INFORMAL = nullptr;

Operator * OperatorManager::OPERATOR_TRACE = nullptr;

Operator * OperatorManager::OPERATOR_DEBUG = nullptr;

Operator * OperatorManager::OPERATOR_COMMENT = nullptr;

Operator * OperatorManager::OPERATOR_QUOTE = nullptr;

Operator * OperatorManager::OPERATOR_META_EVAL = nullptr;
Operator * OperatorManager::OPERATOR_META_RUN = nullptr;


/*
 *******************************************************************************
 * AVM UFI STATEMENT
 *******************************************************************************
 */
Operator * OperatorManager::OPERATOR_UFI = nullptr;


/*
 *******************************************************************************
 * AVM FORM CONSTRUCTOR STATEMENT
 *******************************************************************************
 */
Operator * OperatorManager::OPERATOR_CTOR = nullptr;

/*
 *******************************************************************************
 * AVM MACHINE SELF SUPER
 *******************************************************************************
 */
Operator * OperatorManager::OPERATOR_SELF = nullptr;

Operator * OperatorManager::OPERATOR_SUPER = nullptr;

/*
 *******************************************************************************
 * AVM MACHINE MANAGING
 *******************************************************************************
 */
Operator * OperatorManager::OPERATOR_CONTEXT_SWITCHER = nullptr;

Operator * OperatorManager::OPERATOR_PROCESS_STATE_GET = nullptr;
Operator * OperatorManager::OPERATOR_PROCESS_STATE_SET = nullptr;

Operator * OperatorManager::OPERATOR_INIT = nullptr;
Operator * OperatorManager::OPERATOR_FINAL = nullptr;
Operator * OperatorManager::OPERATOR_DESTROY = nullptr;

Operator * OperatorManager::OPERATOR_START = nullptr;
Operator * OperatorManager::OPERATOR_RESTART = nullptr;
Operator * OperatorManager::OPERATOR_STOP = nullptr;

Operator * OperatorManager::OPERATOR_WAIT = nullptr;

Operator * OperatorManager::OPERATOR_SUSPEND = nullptr;
Operator * OperatorManager::OPERATOR_RESUME = nullptr;

Operator * OperatorManager::OPERATOR_IENABLE_INVOKE = nullptr;
Operator * OperatorManager::OPERATOR_ENABLE_INVOKE = nullptr;
Operator * OperatorManager::OPERATOR_ENABLE_SET = nullptr;

Operator * OperatorManager::OPERATOR_IDISABLE_INVOKE = nullptr;
Operator * OperatorManager::OPERATOR_DISABLE_INVOKE = nullptr;
Operator * OperatorManager::OPERATOR_DISABLE_SET = nullptr;
Operator * OperatorManager::OPERATOR_DISABLE_CHILD = nullptr;
Operator * OperatorManager::OPERATOR_DISABLE_SELF = nullptr;
Operator * OperatorManager::OPERATOR_DISABLE_SELVES = nullptr;

Operator * OperatorManager::OPERATOR_IABORT_INVOKE = nullptr;
Operator * OperatorManager::OPERATOR_ABORT_INVOKE = nullptr;
Operator * OperatorManager::OPERATOR_ABORT_SET = nullptr;
Operator * OperatorManager::OPERATOR_ABORT_CHILD = nullptr;
Operator * OperatorManager::OPERATOR_ABORT_SELF = nullptr;
Operator * OperatorManager::OPERATOR_ABORT_SELVES = nullptr;

Operator * OperatorManager::OPERATOR_HISTORY_CLEAR = nullptr;
Operator * OperatorManager::OPERATOR_DEEP_HISTORY_INVOKE = nullptr;
Operator * OperatorManager::OPERATOR_SHALLOW_HISTORY_INVOKE = nullptr;


Operator * OperatorManager::OPERATOR_IRUN = nullptr;
Operator * OperatorManager::OPERATOR_RUN = nullptr;
Operator * OperatorManager::OPERATOR_RTC = nullptr;

Operator * OperatorManager::OPERATOR_INVOKE_NEW = nullptr;

Operator * OperatorManager::OPERATOR_INVOKE_ROUTINE = nullptr;

Operator * OperatorManager::OPERATOR_INVOKE_TRANSITION = nullptr;

Operator * OperatorManager::OPERATOR_INVOKE_METHOD = nullptr;
Operator * OperatorManager::OPERATOR_INVOKE_PROGRAM = nullptr;
Operator * OperatorManager::OPERATOR_INVOKE_FUNCTION = nullptr;

Operator * OperatorManager::OPERATOR_INVOKE_LAMBDA_APPLY = nullptr;
Operator * OperatorManager::OPERATOR_INVOKE_LAMBDA_LET = nullptr;

Operator * OperatorManager::OPERATOR_GOTO = nullptr;

Operator * OperatorManager::OPERATOR_SCHEDULE_INVOKE = nullptr;
Operator * OperatorManager::OPERATOR_SCHEDULE_GET = nullptr;
Operator * OperatorManager::OPERATOR_SCHEDULE_IN = nullptr;
Operator * OperatorManager::OPERATOR_SCHEDULE_SET = nullptr;

Operator * OperatorManager::OPERATOR_DEFER_INVOKE = nullptr;
Operator * OperatorManager::OPERATOR_DEFER_GET = nullptr;
Operator * OperatorManager::OPERATOR_DEFER_SET = nullptr;

Operator * OperatorManager::OPERATOR_FORK = nullptr;
Operator * OperatorManager::OPERATOR_JOIN = nullptr;

Operator * OperatorManager::OPERATOR_INPUT_ENABLED = nullptr;

Operator * OperatorManager::OPERATOR_RDV = nullptr;

Operator * OperatorManager::OPERATOR_SYNCHRONIZE = nullptr;


/*
 *******************************************************************************
 * AVM DATA STATUS
 *******************************************************************************
 */
Operator * OperatorManager::OPERATOR_STATUS_WAS = nullptr;
Operator * OperatorManager::OPERATOR_STATUS_IS = nullptr;
Operator * OperatorManager::OPERATOR_STATUS_BEING = nullptr;
Operator * OperatorManager::OPERATOR_STATUS_WILL = nullptr;

Operator * OperatorManager::OPERATOR_CHANGED = nullptr;
Operator * OperatorManager::OPERATOR_CHANGED_TO = nullptr;


/*
 *******************************************************************************
 * AVM PROGRAM SCHEDULING
 *******************************************************************************
 */
Operator * OperatorManager::OPERATOR_ASYNCHRONOUS = nullptr;
Operator * OperatorManager::OPERATOR_STRONG_SYNCHRONOUS = nullptr;
Operator * OperatorManager::OPERATOR_WEAK_SYNCHRONOUS = nullptr;

Operator * OperatorManager::OPERATOR_INTERLEAVING = nullptr;
Operator * OperatorManager::OPERATOR_PARTIAL_ORDER = nullptr;

Operator * OperatorManager::OPERATOR_PARALLEL = nullptr;

// Optimized version of concurrency for RDV synchronization
Operator * OperatorManager::OPERATOR_RDV_ASYNCHRONOUS = nullptr;
Operator * OperatorManager::OPERATOR_RDV_STRONG_SYNCHRONOUS = nullptr;
Operator * OperatorManager::OPERATOR_RDV_WEAK_SYNCHRONOUS = nullptr;

Operator * OperatorManager::OPERATOR_RDV_INTERLEAVING = nullptr;
Operator * OperatorManager::OPERATOR_RDV_PARTIAL_ORDER = nullptr;

Operator * OperatorManager::OPERATOR_RDV_PARALLEL = nullptr;


Operator * OperatorManager::OPERATOR_EXCLUSIVE = nullptr;
Operator * OperatorManager::OPERATOR_NONDETERMINISM = nullptr;

Operator * OperatorManager::OPERATOR_PRIOR_GT = nullptr;
Operator * OperatorManager::OPERATOR_PRIOR_LT = nullptr;

Operator * OperatorManager::OPERATOR_SCHEDULE_AND_THEN = nullptr;
Operator * OperatorManager::OPERATOR_SCHEDULE_OR_ELSE = nullptr;

Operator * OperatorManager::OPERATOR_ATOMIC_SEQUENCE = nullptr;

Operator * OperatorManager::OPERATOR_SEQUENCE = nullptr;
Operator * OperatorManager::OPERATOR_SEQUENCE_SIDE = nullptr;
Operator * OperatorManager::OPERATOR_SEQUENCE_WEAK = nullptr;

Operator * OperatorManager::OPERATOR_PRODUCT = nullptr;


/*
 *******************************************************************************
 * AVM BUFFER MANAGING
 *******************************************************************************
 */
Operator * OperatorManager::OPERATOR_UPDATE_BUFFER = nullptr;


/*
 *******************************************************************************
 * LAMBDA STATEMENT
 *******************************************************************************
 */
Operator * OperatorManager::OPERATOR_APPLY = nullptr;

Operator * OperatorManager::OPERATOR_LAMBDA = nullptr;


/*
 *******************************************************************************
 * LET STATEMENT
 *******************************************************************************
 */
Operator * OperatorManager::OPERATOR_LET = nullptr;


/*
 *******************************************************************************
 * AVM PRIMITIVE STATEMENT
 *******************************************************************************
 */
Operator * OperatorManager::OPERATOR_ASSIGN = nullptr;
Operator * OperatorManager::OPERATOR_ASSIGN_AFTER = nullptr;
Operator * OperatorManager::OPERATOR_ASSIGN_OP = nullptr;
Operator * OperatorManager::OPERATOR_ASSIGN_OP_AFTER = nullptr;
Operator * OperatorManager::OPERATOR_ASSIGN_REF = nullptr;
Operator * OperatorManager::OPERATOR_ASSIGN_MACRO = nullptr;

Operator * OperatorManager::OPERATOR_ASSIGN_NEWFRESH = nullptr;

Operator * OperatorManager::OPERATOR_ASSIGN_RESET = nullptr;


Operator * OperatorManager::OPERATOR_GUARD = nullptr;
Operator * OperatorManager::OPERATOR_TIMED_GUARD = nullptr;

Operator * OperatorManager::OPERATOR_EVENT = nullptr;
Operator * OperatorManager::OPERATOR_CHECK_SAT = nullptr;


Operator * OperatorManager::OPERATOR_INPUT = nullptr;
Operator * OperatorManager::OPERATOR_INPUT_FROM = nullptr;

Operator * OperatorManager::OPERATOR_INPUT_SAVE = nullptr;

// Optimized version of INPUT
Operator * OperatorManager::OPERATOR_INPUT_VAR = nullptr;
Operator * OperatorManager::OPERATOR_INPUT_FLOW = nullptr;

Operator * OperatorManager::OPERATOR_INPUT_ENV = nullptr;
Operator * OperatorManager::OPERATOR_INPUT_BUFFER = nullptr;
Operator * OperatorManager::OPERATOR_INPUT_RDV = nullptr;
Operator * OperatorManager::OPERATOR_INPUT_BROADCAST = nullptr;
Operator * OperatorManager::OPERATOR_INPUT_DELEGATE = nullptr;


Operator * OperatorManager::OPERATOR_OUTPUT = nullptr;
Operator * OperatorManager::OPERATOR_OUTPUT_TO = nullptr;

// Optimized version of OUTPUT
Operator * OperatorManager::OPERATOR_OUTPUT_VAR = nullptr;
Operator * OperatorManager::OPERATOR_OUTPUT_FLOW = nullptr;

Operator * OperatorManager::OPERATOR_OUTPUT_ENV = nullptr;
Operator * OperatorManager::OPERATOR_OUTPUT_BUFFER = nullptr;
Operator * OperatorManager::OPERATOR_OUTPUT_RDV = nullptr;
Operator * OperatorManager::OPERATOR_OUTPUT_BROADCAST = nullptr;
Operator * OperatorManager::OPERATOR_OUTPUT_DELEGATE = nullptr;


Operator * OperatorManager::OPERATOR_PRESENT = nullptr;
Operator * OperatorManager::OPERATOR_ABSENT = nullptr;


Operator * OperatorManager::OPERATOR_IF = nullptr;
Operator * OperatorManager::OPERATOR_IFE = nullptr;

Operator * OperatorManager::OPERATOR_FOR = nullptr;
Operator * OperatorManager::OPERATOR_FOREACH = nullptr;
Operator * OperatorManager::OPERATOR_WHILE_DO = nullptr;
Operator * OperatorManager::OPERATOR_DO_WHILE = nullptr;

Operator * OperatorManager::OPERATOR_BREAK = nullptr;
Operator * OperatorManager::OPERATOR_CONTINUE = nullptr;
Operator * OperatorManager::OPERATOR_RETURN = nullptr;
Operator * OperatorManager::OPERATOR_EXIT = nullptr;

Operator * OperatorManager::OPERATOR_STEP_MARK = nullptr;


/*
 *******************************************************************************
 * AVM PREDICAT EXPRESSION
 *******************************************************************************
 */
Operator * OperatorManager::OPERATOR_EXISTS = nullptr;
Operator * OperatorManager::OPERATOR_FORALL = nullptr;

Operator * OperatorManager::OPERATOR_NOT = nullptr;

Operator * OperatorManager::OPERATOR_AND = nullptr;
Operator * OperatorManager::OPERATOR_AND_THEN = nullptr;

Operator * OperatorManager::OPERATOR_NAND = nullptr;

Operator * OperatorManager::OPERATOR_XAND = nullptr;

Operator * OperatorManager::OPERATOR_OR = nullptr;
Operator * OperatorManager::OPERATOR_OR_ELSE = nullptr;

Operator * OperatorManager::OPERATOR_NOR = nullptr;

Operator * OperatorManager::OPERATOR_XOR = nullptr;
Operator * OperatorManager::OPERATOR_XNOR = nullptr;

Operator * OperatorManager::OPERATOR_IMPLIES = nullptr;


/*
 *******************************************************************************
 * AVM COMPARISON EXPRESSION
 *******************************************************************************
 */
Operator * OperatorManager::OPERATOR_EQ = nullptr;
Operator * OperatorManager::OPERATOR_NEQ = nullptr;

Operator * OperatorManager::OPERATOR_SEQ = nullptr;
Operator * OperatorManager::OPERATOR_NSEQ = nullptr;

Operator * OperatorManager::OPERATOR_LT = nullptr;
Operator * OperatorManager::OPERATOR_LTE = nullptr;
Operator * OperatorManager::OPERATOR_GT = nullptr;
Operator * OperatorManager::OPERATOR_GTE = nullptr;



/*
 *******************************************************************************
 * AVM BITWISE EXPRESSION
 *******************************************************************************
 */
Operator * OperatorManager::OPERATOR_BNOT = nullptr;

Operator * OperatorManager::OPERATOR_BAND = nullptr;
Operator * OperatorManager::OPERATOR_BOR = nullptr;
Operator * OperatorManager::OPERATOR_BXOR = nullptr;

Operator * OperatorManager::OPERATOR_LSHIFT = nullptr;
Operator * OperatorManager::OPERATOR_RSHIFT = nullptr;


/*
 *******************************************************************************
 * AVM ARITHMETIC EXPRESSION
 *******************************************************************************
 */
Operator * OperatorManager::OPERATOR_PLUS = nullptr;
Operator * OperatorManager::OPERATOR_MINUS = nullptr;
Operator * OperatorManager::OPERATOR_UMINUS = nullptr;

Operator * OperatorManager::OPERATOR_MULT = nullptr;
Operator * OperatorManager::OPERATOR_POW = nullptr;

Operator * OperatorManager::OPERATOR_DIV = nullptr;
Operator * OperatorManager::OPERATOR_MOD = nullptr;

Operator * OperatorManager::OPERATOR_MIN = nullptr;
Operator * OperatorManager::OPERATOR_MAX = nullptr;


/*
 *******************************************************************************
 * LOOKUP STATEMENT
 *******************************************************************************
 */
Operator * OperatorManager::OPERATOR_LOOKUP_INT_EXT = nullptr;
Operator * OperatorManager::OPERATOR_LOOKUP_INT = nullptr;
Operator * OperatorManager::OPERATOR_LOOKUP_NEAREST = nullptr;
Operator * OperatorManager::OPERATOR_LOOKUP_BELOW = nullptr;
Operator * OperatorManager::OPERATOR_LOOKUP_ABOVE = nullptr;
Operator * OperatorManager::OPERATOR_LOOKUP2D_INT_EXT = nullptr;


/*
 *******************************************************************************
 * AVM MATHEMATICAL FUNCTION
 *******************************************************************************
 */
 // RANDOM
Operator * OperatorManager::OPERATOR_RANDOM = nullptr;

// ROUNDING
Operator * OperatorManager::OPERATOR_ABS = nullptr;

Operator * OperatorManager::OPERATOR_CEIL = nullptr;
Operator * OperatorManager::OPERATOR_FLOOR = nullptr;
Operator * OperatorManager::OPERATOR_ROUND = nullptr;
Operator * OperatorManager::OPERATOR_TRUNCATE = nullptr;


// EXP - LOG
Operator * OperatorManager::OPERATOR_SQRT = nullptr;

Operator * OperatorManager::OPERATOR_EXP = nullptr;
Operator * OperatorManager::OPERATOR_LN = nullptr;
Operator * OperatorManager::OPERATOR_LOG = nullptr;

// TRIGONOMETRIC
Operator * OperatorManager::OPERATOR_SIN = nullptr;
Operator * OperatorManager::OPERATOR_COS = nullptr;
Operator * OperatorManager::OPERATOR_TAN = nullptr;

Operator * OperatorManager::OPERATOR_SINH = nullptr;
Operator * OperatorManager::OPERATOR_COSH = nullptr;
Operator * OperatorManager::OPERATOR_TANH = nullptr;

Operator * OperatorManager::OPERATOR_ASIN = nullptr;
Operator * OperatorManager::OPERATOR_ACOS = nullptr;
Operator * OperatorManager::OPERATOR_ATAN = nullptr;
Operator * OperatorManager::OPERATOR_ATAN2 = nullptr;

Operator * OperatorManager::OPERATOR_ASINH = nullptr;
Operator * OperatorManager::OPERATOR_ACOSH = nullptr;
Operator * OperatorManager::OPERATOR_ATANH = nullptr;


/*
 *******************************************************************************
 * AVM STRING / COLLECTION OPERATOR
 *******************************************************************************
 */
Operator * OperatorManager::OPERATOR_CONTAINS = nullptr;

Operator * OperatorManager::OPERATOR_IN = nullptr;
Operator * OperatorManager::OPERATOR_NOTIN = nullptr;

Operator * OperatorManager::OPERATOR_SUBSET = nullptr;
Operator * OperatorManager::OPERATOR_SUBSETEQ = nullptr;

Operator * OperatorManager::OPERATOR_INTERSECT = nullptr;

Operator * OperatorManager::OPERATOR_STARTS_WITH = nullptr;
Operator * OperatorManager::OPERATOR_ENDS_WITH = nullptr;

Operator * OperatorManager::OPERATOR_CONCAT = nullptr;

Operator * OperatorManager::OPERATOR_APPEND = nullptr;

Operator * OperatorManager::OPERATOR_REMOVE = nullptr;
Operator * OperatorManager::OPERATOR_CLEAR = nullptr;

Operator * OperatorManager::OPERATOR_RESIZE = nullptr;

Operator * OperatorManager::OPERATOR_SELECT = nullptr;

Operator * OperatorManager::OPERATOR_PUSH = nullptr;
Operator * OperatorManager::OPERATOR_ASSIGN_TOP = nullptr;
Operator * OperatorManager::OPERATOR_TOP = nullptr;
Operator * OperatorManager::OPERATOR_POP = nullptr;
Operator * OperatorManager::OPERATOR_POP_FROM = nullptr;

Operator * OperatorManager::OPERATOR_EMPTY = nullptr;
Operator * OperatorManager::OPERATOR_NONEMPTY = nullptr;
Operator * OperatorManager::OPERATOR_SINGLETON = nullptr;
Operator * OperatorManager::OPERATOR_POPULATED = nullptr;
Operator * OperatorManager::OPERATOR_FULL = nullptr;

Operator * OperatorManager::OPERATOR_SIZE = nullptr;


/*
 *******************************************************************************
 * IOLTL BEHAVIORAL PREDICAT
 *******************************************************************************
 */
Operator * OperatorManager::OPERATOR_GLOBALLY = nullptr;
Operator * OperatorManager::OPERATOR_UNTIL = nullptr;
Operator * OperatorManager::OPERATOR_NEXT = nullptr;
Operator * OperatorManager::OPERATOR_EVENTUALLY = nullptr;
Operator * OperatorManager::OPERATOR_RELEASES = nullptr;
Operator * OperatorManager::OPERATOR_OBS = nullptr;


/*
 *******************************************************************************
 * IOLTL LOGICAL PREDICAT
 *******************************************************************************
 */
Operator * OperatorManager::OPERATOR_AND_T = nullptr;
Operator * OperatorManager::OPERATOR_OR_T = nullptr;
Operator * OperatorManager::OPERATOR_NOT_T = nullptr;
Operator * OperatorManager::OPERATOR_IMP_T = nullptr;



/**
 * LOADER
 */
void OperatorManager::load()
{

// Operator print string format: NAME_ID, ALGEBRA_*, *FIX, SYMBOL, MIXFIX, QEPCAD

#define NEW_STATEMENT( OP , NAME )  \
	OPERATOR_##OP = newOpStatement( \
			AVM_OPCODE_##OP , AVM_OPCODE_##OP , "operator::" #OP , NAME )

#define NEW_STATEMENT_INVOKE( OP , NAME )     \
	OPERATOR_##OP##_INVOKE = newOpStatement(  \
			AVM_OPCODE_##OP##_INVOKE , AVM_OPCODE_##OP##_INVOKE ,  \
			"operator::" #OP "#INVOKE" , NAME )

#define NEW_STATEMENT_DESC( OP , DESC , STR )  \
	OPERATOR_##OP##_##DESC = newOpStatement(   \
			AVM_OPCODE_##OP##_##DESC , "operator::" #OP , STR )

#define NEW_STATEMENT_DIESE( OP , DIESE , NAME )  \
	OPERATOR_##OP##_##DIESE = newOpStatement(     \
			AVM_OPCODE_##OP##_##DIESE , AVM_OPCODE_##OP##_##DIESE ,  \
			"operator::" #OP "#" #DIESE , NAME )

#define NEW_STATEMENT_OPTI( OP , OPTI , NAME )  \
	OPERATOR_##OP##_##OPTI = newOpStatement( AVM_OPCODE_##OP ,  \
			AVM_OPCODE_##OP##_##OPTI , "operator::" #OP "_" #OPTI , NAME )


#define NEW_FUNCTION( OP , NAME )  \
	OPERATOR_##OP = newOperator( AVM_OPCODE_##OP  , AVM_OPCODE_##OP   ,  \
			"operator::" #OP , NAME , ALGEBRA_STD , NOTATION_FUNCTION ,  \
			NAME , NAME "(_)" , NAME )


#define NEW_OP_ASSOC_COM( OP , NAME , SYMBOL )  \
	OPERATOR_##OP = newOperatorAssocCom( AVM_OPCODE_##OP ,  \
			AVM_OPCODE_##OP , "operator::" #OP , NAME , SYMBOL )

#define NEW_OP_ASSOC_COM_FULL( OP , NAME , SYMBOL , MIXFIX, QEPCAD )  \
	OPERATOR_##OP = newOperatorAssocCom( AVM_OPCODE_##OP ,  \
			"operator::" #OP , NAME , SYMBOL , MIXFIX, QEPCAD )

#define NEW_OP_ASSOC_COM_RDV( OP , NAME , SYMBOL )  \
	OPERATOR_RDV_##OP = newOperatorAssocCom(            \
			AVM_OPCODE_RDV_##OP , AVM_OPCODE_RDV##_##OP , \
			"operator::RDV_" #OP , NAME , SYMBOL )


#define NEW_OP_ASSOC( OP , NAME , SYMBOL )  \
	OPERATOR_##OP = newOperatorAssoc(        \
			AVM_OPCODE_##OP , "operator::" #OP , NAME , SYMBOL )

#define NEW_OP_LEFT_ASSOC( OP , NAME , SYMBOL )  \
	OPERATOR_##OP = newOperatorLeftAssoc(        \
			AVM_OPCODE_##OP , "operator::" #OP , NAME , SYMBOL )

#define NEW_OP_RIGHT_ASSOC( OP , NAME , SYMBOL )  \
	OPERATOR_##OP = newOperatorRightAssoc(        \
			AVM_OPCODE_##OP , "operator::" #OP , NAME , SYMBOL )

#define NEW_OP_RIGHT_ASSOC_DIESE( OP , DIESE , NAME , SYMBOL )  \
	OPERATOR_##OP##_##DIESE = newOperatorRightAssoc(  \
			AVM_OPCODE_##OP##_##DIESE ,  \
			"operator::" #OP "#" #DIESE , NAME , SYMBOL )


#define NEW_OP_INFIX( OP , NAME )  \
	OPERATOR_##OP = newOperatorStdInfix(    \
			AVM_OPCODE_##OP , "operator::" #OP , NAME , NAME )

#define NEW_OP_INFIX_FULL( OP , NAME , SYMBOL , MIXFIX, QEPCAD )  \
	OPERATOR_##OP = newOperatorStdInfix( AVM_OPCODE_##OP ,  \
			"operator::" #OP , NAME , SYMBOL , MIXFIX, QEPCAD )


#define NEW_OP_PREFIX( OP , NAME )  \
	OPERATOR_##OP = newOperatorStdPrefix(     \
			AVM_OPCODE_##OP , "operator::" #OP , NAME , NAME )

#define NEW_OP_PREFIX_SYMB( OP , NAME , SYMBOL )  \
	OPERATOR_##OP = newOperatorStdPrefix(     \
			AVM_OPCODE_##OP , "operator::" #OP , NAME , SYMBOL )

#define NEW_OP_PREFIX_FULL( OP , NAME , SYMBOL , MIXFIX, QEPCAD )  \
	OPERATOR_##OP = newOperatorStdPrefix( AVM_OPCODE_##OP ,  \
			"operator::" #OP , NAME , SYMBOL , MIXFIX, QEPCAD )


	/*
	 ***************************************************************************
	 * AVM NULL / NOP STATEMENT
	 ***************************************************************************
	 */
	NEW_STATEMENT( NULL , "null" );

	NEW_STATEMENT( NOP  , "nop" );


	/*
	 ***************************************************************************
	 * AVM META STATEMENT
	 ***************************************************************************
	 */
	NEW_STATEMENT( INFORMAL  , "@informal" );
	NEW_STATEMENT( TRACE     , "@trace"    );
	NEW_STATEMENT( DEBUG     , "@debug"    );
	NEW_STATEMENT( COMMENT   , "@comment"  );
	NEW_STATEMENT( QUOTE     , "quote"     );
	NEW_STATEMENT( META_EVAL , "meta_eval" );
	NEW_STATEMENT( META_RUN  , "meta_run"  );

	/*
	 ***************************************************************************
	 * AVM UFI STATEMENT
	 ***************************************************************************
	 */
	NEW_STATEMENT( UFI , "ufi" );

	/*
	 ***************************************************************************
	 * AVM CONSTRUCTOR & CAST STATEMENT
	 ***************************************************************************
	 */
	NEW_STATEMENT( CTOR , "ctor" );

	/*
	 ***************************************************************************
	 * AVM MACHINE SELF
	 ***************************************************************************
	 */
	NEW_FUNCTION( SELF , "self" );

	NEW_FUNCTION( SUPER , "super" );

	/*
	 ***************************************************************************
	 * AVM MACHINE MANAGING
	 ***************************************************************************
	 */
	NEW_STATEMENT( CONTEXT_SWITCHER, "ctx" );

	NEW_STATEMENT( PROCESS_STATE_GET, "process#state#get" );
	NEW_STATEMENT( PROCESS_STATE_SET, "process#state#set" );


	NEW_STATEMENT( INIT    , "init"    );
	NEW_STATEMENT( FINAL   , "final"   );
	NEW_STATEMENT( DESTROY , "destroy" );

	NEW_STATEMENT( START   , "start"   );
	NEW_STATEMENT( RESTART , "restart" );

	NEW_STATEMENT( STOP , "stop" );
	NEW_STATEMENT( WAIT , "wait" );

	NEW_STATEMENT( SUSPEND , "suspend" );
	NEW_STATEMENT( RESUME  , "resume"  );

	NEW_STATEMENT_INVOKE( IENABLE , "ienable" );
	NEW_STATEMENT_INVOKE( ENABLE  , "enable"  );

	NEW_STATEMENT_DIESE( ENABLE , SET , "enable#set" );

	NEW_STATEMENT_INVOKE( IDISABLE , "idisable" );
	NEW_STATEMENT_INVOKE( DISABLE  , "disable"  );

	NEW_STATEMENT_DIESE( DISABLE  , SET    , "disable#set"   );
	NEW_STATEMENT_DIESE( DISABLE  , CHILD  , "disable#child" );
	NEW_STATEMENT_DIESE( DISABLE  , SELF   , "disable#self"  );
	NEW_STATEMENT_DIESE( DISABLE  , SELVES , "disable#selves");

	NEW_STATEMENT_INVOKE( IABORT , "iabort" );
	NEW_STATEMENT_INVOKE( ABORT  , "abort"  );

	NEW_STATEMENT_DIESE( ABORT , SET    , "abort#set"   );
	NEW_STATEMENT_DIESE( ABORT , CHILD  , "abort#child" );
	NEW_STATEMENT_DIESE( ABORT , SELF   , "abort#self"  );
	NEW_STATEMENT_DIESE( ABORT , SELVES , "abort#selves");

	NEW_STATEMENT_DIESE( HISTORY , CLEAR  , "history#clear"          );
	NEW_STATEMENT_INVOKE( DEEP_HISTORY    , "deep_history#invoke"    );
	NEW_STATEMENT_INVOKE( SHALLOW_HISTORY , "shallow_history#invoke" );

	NEW_STATEMENT( IRUN, "irun");
	NEW_STATEMENT( RUN , "run" );
	NEW_STATEMENT( RTC , "rtc" );

	NEW_STATEMENT( INVOKE_NEW       , "invoke#new"       );

	NEW_STATEMENT( INVOKE_ROUTINE   , "invoke#routine"   );

	NEW_STATEMENT( INVOKE_TRANSITION, "invoke#transition");

	NEW_STATEMENT( INVOKE_METHOD    , "invoke#method"    );
	NEW_STATEMENT( INVOKE_PROGRAM   , "invoke#program"   );
	NEW_STATEMENT( INVOKE_FUNCTION  , "invoke#function"  );

	NEW_STATEMENT( INVOKE_LAMBDA_APPLY, "invoke#apply"   );
	NEW_STATEMENT( INVOKE_LAMBDA_LET  , "invoke#let"     );

	NEW_STATEMENT( GOTO, "goto");

	NEW_STATEMENT_DIESE( SCHEDULE , INVOKE, "schedule"    );
	NEW_STATEMENT_DIESE( SCHEDULE , GET   , "schedule#get");
	NEW_STATEMENT_DIESE( SCHEDULE , IN    , "schedule#in" );
	NEW_STATEMENT_DIESE( SCHEDULE , SET   , "schedule#set");

	NEW_STATEMENT_DIESE( DEFER , INVOKE, "defer"    );
	NEW_STATEMENT_DIESE( DEFER , GET   , "defer#get");
	NEW_STATEMENT_DIESE( DEFER , SET   , "defer#set");

	NEW_OP_ASSOC_COM( FORK , "fork" , "|fork|" );
	NEW_OP_ASSOC_COM( JOIN , "join" , "|join|" );

	NEW_STATEMENT( INPUT_ENABLED, "input_enabled");

	NEW_STATEMENT( RDV, "rdv");

	NEW_STATEMENT( SYNCHRONIZE, "synchronize");

	/*
	 ***************************************************************************
	 * AVM DATA STATUS
	 ***************************************************************************
	 */
	NEW_FUNCTION( STATUS_WAS   , "status#was"   );
	NEW_FUNCTION( STATUS_IS    , "status#is"    );
	NEW_FUNCTION( STATUS_BEING , "status#being" );
	NEW_FUNCTION( STATUS_WILL  , "status#will"  );
	NEW_FUNCTION( CHANGED      , "changed"      );
	NEW_FUNCTION( CHANGED_TO   , "changed#to"   );

	/*
	 ***************************************************************************
	 * AVM PROGRAM SCHEDULING
	 ***************************************************************************
	 */
	NEW_OP_ASSOC_COM( ASYNCHRONOUS , "|async|" , "|a|");

	NEW_OP_ASSOC_COM( STRONG_SYNCHRONOUS , "|strong_sync|"   , "|and|");

	NEW_OP_ASSOC_COM( WEAK_SYNCHRONOUS   , "|weak_sync|"     , "|or|" );

	NEW_OP_ASSOC_COM( INTERLEAVING       , "|interleaving|"  , "|i|"  );

	NEW_OP_ASSOC_COM( PARTIAL_ORDER      , "|partial_order|" , "|~|"  );

	NEW_OP_ASSOC_COM( PARALLEL           , "|parallel|"      , "|,|"  );

	// Optimized version of concurrency for RDV synchronization
	NEW_OP_ASSOC_COM_RDV( ASYNCHRONOUS      , "|rdv_async|"        , "||a||"  );
	NEW_OP_ASSOC_COM_RDV( STRONG_SYNCHRONOUS, "|rdv_strong_sync|"  , "||and||");

	NEW_OP_ASSOC_COM_RDV( WEAK_SYNCHRONOUS  , "|rdv_weak_sync|"    , "||or||" );

	NEW_OP_ASSOC_COM_RDV( INTERLEAVING      , "|rdv_interleaving|" , "||i||"  );

	NEW_OP_ASSOC_COM( RDV_PARTIAL_ORDER     , "|rdv_partial_order|", "||~||"  );

	NEW_OP_ASSOC_COM_RDV( PARALLEL          , "rdv_parallel"       , "||,||"  );

	NEW_OP_ASSOC_COM( EXCLUSIVE             , "exclusive"          , "|xor|"  );

	NEW_OP_ASSOC_COM( NONDETERMINISM        , "indeterminism"      , "|/\\|"  );

	NEW_OP_LEFT_ASSOC( PRIOR_GT , "prior_gt" , "|>|");
	NEW_OP_LEFT_ASSOC( PRIOR_LT , "prior_lt" , "|<|");

	NEW_OP_ASSOC_COM( SCHEDULE_AND_THEN , "|and#then|" , "|and#then|");
	NEW_OP_ASSOC_COM( SCHEDULE_OR_ELSE  , "|or#else|"  , "|or#else|" );

	NEW_OP_ASSOC( ATOMIC_SEQUENCE , "atomic"   , "|§|"  );
	NEW_OP_ASSOC( SEQUENCE        , "seq"      , "|;|"  );
	NEW_OP_ASSOC( SEQUENCE_SIDE   , "seq_side" , "|/;|" );
	NEW_OP_ASSOC( SEQUENCE_WEAK   , "seq_weak" , "|;;|" );

	NEW_OP_ASSOC_COM( PRODUCT , "prod" , "|x|");

	/*
	 ***************************************************************************
	 * AVM BUFFER MANAGING
	 ***************************************************************************
	 */
	NEW_FUNCTION( UPDATE_BUFFER , "UpdateBuffer" );

	/*
	 ***************************************************************************
	 * LAMBDA STATEMENT
	 ***************************************************************************
	 */
	NEW_FUNCTION( APPLY  , "apply"  );
	NEW_FUNCTION( LAMBDA , "lambda" );

	/*
	 ***************************************************************************
	 * LET STATEMENT
	 ***************************************************************************
	 */
	NEW_OP_PREFIX( LET , "let" );

	/*
	 ***************************************************************************
	 * LOOKUP STATEMENT
	 ***************************************************************************
	 */
	NEW_FUNCTION( LOOKUP_INT_EXT   , "lookupie"   );
	NEW_FUNCTION( LOOKUP_INT       , "lookupi"    );
	NEW_FUNCTION( LOOKUP_NEAREST   , "lookupn"    );
	NEW_FUNCTION( LOOKUP_BELOW     , "lookupb"    );
	NEW_FUNCTION( LOOKUP_ABOVE     , "lookupa"    );
	NEW_FUNCTION( LOOKUP2D_INT_EXT , "lookup2die" );


	/*
	 ***************************************************************************
	 * AVM PRIMITIVE STATEMENT
	 ***************************************************************************
	 */
	NEW_OP_RIGHT_ASSOC( ASSIGN , "assign"          , ":=" );

	NEW_OP_RIGHT_ASSOC_DIESE( ASSIGN , AFTER   , "assign#after"   , "=:" );
	NEW_OP_RIGHT_ASSOC_DIESE( ASSIGN , OP      , "assign#op"      , ":=" );
	NEW_OP_RIGHT_ASSOC_DIESE( ASSIGN , OP_AFTER, "assign#op#after", "=:" );
	NEW_OP_RIGHT_ASSOC_DIESE( ASSIGN , REF     , "assign#ref"     , "<-" );
	NEW_OP_RIGHT_ASSOC_DIESE( ASSIGN , MACRO   , "assign#macro"   , "::=");

	NEW_FUNCTION( ASSIGN_NEWFRESH , "newfresh" );
	NEW_FUNCTION( ASSIGN_RESET    , "reset"    );

	NEW_STATEMENT( GUARD      , "guard"     );
	NEW_STATEMENT( TIMED_GUARD, "tguard"    );

	NEW_STATEMENT( EVENT      , "event"     );

	NEW_STATEMENT( CHECK_SAT  , "check_sat" );

	NEW_STATEMENT( INPUT      , "input"     );

	NEW_STATEMENT( INPUT_FROM , "input_from");
	NEW_STATEMENT( INPUT_SAVE , "input#save");

	// Optimized version of INPUT
	NEW_STATEMENT_OPTI( INPUT , VAR   , "input#var"   );
	NEW_STATEMENT_OPTI( INPUT , FLOW  , "input#flow"  );

	NEW_STATEMENT_OPTI( INPUT , ENV   , "input#env"   );
	NEW_STATEMENT_OPTI( INPUT , BUFFER, "input#buffer");
	NEW_STATEMENT_OPTI( INPUT , RDV   , "input#rdv"   );

	NEW_STATEMENT_OPTI( INPUT , BROADCAST, "input#broadcast");
	NEW_STATEMENT_OPTI( INPUT , DELEGATE , "input#delegate" );

	NEW_STATEMENT( OUTPUT, "output");

	NEW_STATEMENT( OUTPUT_TO, "output_to");

	// Optimized version of OUTPUT
	NEW_STATEMENT_OPTI( OUTPUT , VAR   , "output#var"   );
	NEW_STATEMENT_OPTI( OUTPUT , FLOW  , "output#flow"  );

	NEW_STATEMENT_OPTI( OUTPUT , ENV   , "output#env"   );
	NEW_STATEMENT_OPTI( OUTPUT , BUFFER, "output#buffer");
	NEW_STATEMENT_OPTI( OUTPUT , RDV   , "output#rdv"   );

	NEW_STATEMENT_OPTI( OUTPUT , BROADCAST, "output#broadcast");
	NEW_STATEMENT_OPTI( OUTPUT , DELEGATE , "output#delegate" );

	NEW_STATEMENT( PRESENT, "present");
	NEW_STATEMENT( ABSENT , "absent" );

	NEW_OP_PREFIX(IF  , "if"  );
	NEW_OP_PREFIX(IFE , "ife" );

	NEW_STATEMENT( FOR       , "for"       );
	NEW_STATEMENT( FOREACH   , "foreach"   );
	NEW_STATEMENT( WHILE_DO  , "while_do"  );
	NEW_STATEMENT( DO_WHILE  , "do_while"  );

	NEW_STATEMENT( BREAK     , "break"     );
	NEW_STATEMENT( CONTINUE  , "continue"  );

	NEW_STATEMENT( RETURN    , "return"    );
	NEW_STATEMENT( EXIT      , "exit"      );

	NEW_STATEMENT( STEP_MARK , "step_mark" );

	/*
	 ***************************************************************************
	 * AVM PREDICAT EXPRESSION
	 ***************************************************************************
	 */
	NEW_OP_PREFIX( EXISTS  , "exists" );
	NEW_OP_PREFIX( FORALL , "forall" );

	NEW_OP_PREFIX_FULL(NOT , "not", "!", "!_", "~");

	NEW_OP_ASSOC_COM_FULL( AND , "and" , "&&", "_&_", "/\\");

	NEW_OP_INFIX( AND_THEN , "and#then" );

	NEW_OP_ASSOC_COM( NAND , "nand" , "nand" );
	NEW_OP_ASSOC_COM( XAND , "xand" , "xand" );

	NEW_OP_ASSOC_COM_FULL( OR , "or" , "||", "_|_", "\\/");

	NEW_OP_INFIX( OR_ELSE , "or#else" );

	NEW_OP_ASSOC_COM( NOR  , "nor"  , "nor"  );
	NEW_OP_ASSOC_COM( XOR  , "xor"  , "xor"  );
	NEW_OP_ASSOC_COM( XNOR , "xnor" , "xnor" );

	NEW_OP_ASSOC_COM( IMPLIES , "implies" , "=>" );

	/*
	 ***************************************************************************
	 * AVM COMPARISON EXPRESSION
	 ***************************************************************************
	 */
	NEW_OP_INFIX_FULL( SEQ  , "seq"  , "===", "_===_", "===");
	NEW_OP_INFIX_FULL( NSEQ , "nseq" , "=!=", "_=!=_", "=/=");

	/*
	 ***************************************************************************
	 * AVM COMPARISON EXPRESSION
	 ***************************************************************************
	 */
	NEW_OP_INFIX_FULL( EQ  , "eq"  , "==", "_==_", "=" );
	NEW_OP_INFIX_FULL( NEQ , "neq" , "!=", "_!=_", "/=");

	NEW_OP_INFIX_FULL( LT  , "lt"  , "<" , "_<_" , "<" );
	NEW_OP_INFIX_FULL( LTE , "lte" , "<=", "_<=_", "<=");

	NEW_OP_INFIX_FULL( GT  , "gt"  , ">" , "_>_" , ">" );
	NEW_OP_INFIX_FULL( GTE , "gte" , ">=", "_>=_", ">=");

	/*
	 ***************************************************************************
	 * AVM BITWISE EXPRESSION
	 ***************************************************************************
	 */
	NEW_OP_PREFIX_FULL( BNOT , "bnot" , "~" , "_bnot_", "bnot");

	NEW_OP_INFIX( BAND , "band" );
	NEW_OP_INFIX( BOR  , "bor"  );
	NEW_OP_INFIX( BXOR , "bxor" );

	NEW_OP_INFIX_FULL( LSHIFT , "lshift" , "<<", "_lshift_", "lshift");
	NEW_OP_INFIX_FULL( RSHIFT , "rshift" , ">>", "_rshift_", "rshift");

	/*
	 ***************************************************************************
	 * AVM ARITHMETIC EXPRESSION
	 ***************************************************************************
	 */
	NEW_OP_ASSOC_COM( PLUS , "plus" , "+");

	NEW_OP_LEFT_ASSOC( MINUS , "minus" , "-");

	NEW_OP_PREFIX_SYMB( UMINUS , "uminus" , "-");

	NEW_OP_ASSOC_COM_FULL( MULT , "mult" , "*", "_*_", " ");

	NEW_OP_RIGHT_ASSOC( POW  , "pow"  , "^");

	NEW_OP_LEFT_ASSOC( DIV , "div" , "/");
	NEW_OP_LEFT_ASSOC( MOD , "mod" , "%");

	NEW_OP_ASSOC_COM( MIN , "min" , "min" );
	NEW_OP_ASSOC_COM( MAX , "max" , "max" );

	/*
	 ***************************************************************************
	 * AVM MATHEMATICAL FUNCTION
	 ***************************************************************************
	 */
	// RANDOM
	NEW_FUNCTION( RANDOM , "random" );

	// ABS
	NEW_FUNCTION( ABS    , "abs"  );

	// ROUNDING
	NEW_FUNCTION( CEIL  , "ceil"  );
	NEW_FUNCTION( FLOOR , "floor" );
	NEW_FUNCTION( ROUND , "round" );

	NEW_FUNCTION( TRUNCATE , "trunc" );

	// EXP - LOG
	NEW_FUNCTION( SQRT  , "sqrt"  );
	NEW_FUNCTION( EXP   , "exp"   );
	NEW_FUNCTION( LN    , "ln"    );
	NEW_FUNCTION( LOG   , "log"   );


	// TRIGONOMETRIC
	NEW_FUNCTION( SIN   , "sin"   );
	NEW_FUNCTION( COS   , "cos"   );
	NEW_FUNCTION( TAN   , "tan"   );

	NEW_FUNCTION( SINH  , "sinh"  );
	NEW_FUNCTION( COSH  , "cosh"  );
	NEW_FUNCTION( TANH  , "tanh"  );

	NEW_FUNCTION( ASIN  , "asin"  );
	NEW_FUNCTION( ACOS  , "acos"  );
	NEW_FUNCTION( ATAN  , "atan"  );

	NEW_FUNCTION( ATAN2 , "atan2" );

	NEW_FUNCTION( ASINH , "asinh" );
	NEW_FUNCTION( ACOSH , "acosh" );
	NEW_FUNCTION( ATANH , "atanh" );

	/*
	 ***************************************************************************
	 * AVM STRING / COLLECTION OPERATOR
	 ***************************************************************************
	 */
	NEW_OP_INFIX( CONTAINS , "contains" );

	NEW_OP_INFIX( IN    , "in"    );
	NEW_OP_INFIX( NOTIN , "notin" );

	NEW_OP_INFIX( SUBSET   , "subset"   );
	NEW_OP_INFIX( SUBSETEQ , "subseteq" );

	NEW_OP_INFIX( INTERSECT , "intersect" );

	NEW_OP_INFIX( STARTS_WITH , "start_with" );
	NEW_OP_INFIX( ENDS_WITH   , "end_with"   );

	NEW_OP_INFIX( CONCAT , "concat"  );
	NEW_OP_PREFIX( APPEND , "append" );
	NEW_OP_PREFIX( REMOVE , "remove" );
	NEW_OP_PREFIX( CLEAR  , "clear"  );
	NEW_OP_PREFIX( RESIZE , "resize" );
	NEW_OP_PREFIX( SELECT , "select" );

	NEW_OP_PREFIX_SYMB( PUSH , "push" , "<=<");

	NEW_OP_PREFIX_SYMB( ASSIGN_TOP , "assign_top" , "^=<");

	NEW_OP_PREFIX_SYMB( TOP , "top" , "^=>");
	NEW_OP_PREFIX_SYMB( POP , "pop" , ">=>");

	NEW_OP_PREFIX_SYMB( POP_FROM , "pop_from" , ">?>");

	NEW_FUNCTION( EMPTY     , "empty"     );
	NEW_FUNCTION( NONEMPTY  , "nonempty"  );
	NEW_FUNCTION( SINGLETON , "singleton" );
	NEW_FUNCTION( POPULATED , "populated" );

	NEW_FUNCTION( FULL      , "full"      );
	NEW_FUNCTION( SIZE      , "size"      );

	/*
	 ***************************************************************************
	 * IOLTL BEHAVIORAL PREDICAT
	 ***************************************************************************
	 */
	NEW_OP_PREFIX( GLOBALLY , "globally" );
	NEW_OP_INFIX ( UNTIL    , "until"    );
	NEW_OP_PREFIX( NEXT     , "next"     );

	NEW_OP_PREFIX_SYMB( EVENTUALLY , "eventually" , "evtly");
	NEW_OP_PREFIX_SYMB( RELEASES   , "releases"   , "rels" );

	NEW_OP_PREFIX( OBS , "@observe" );


	/*
	 ***************************************************************************
	 * IOLTL LOGICAL PREDICAT
	 ***************************************************************************
	 */
	NEW_OP_INFIX_FULL ( AND_T , "and_t" , "&", "_&_", " /\\");
	NEW_OP_INFIX_FULL ( OR_T  , "or_t"  , "|", "_|_", "OR-T");

	NEW_OP_PREFIX_FULL( NOT_T , "not_t" , "!", "!_", "NOT-T");

	NEW_OP_INFIX_FULL ( IMP_T , "imp_t" , "->", "_->_", "IMPLIES-T");
}


/**
 * DISPOSER
 */
void OperatorManager::dispose()
{
	theOperatorsMap.clear();

	TABLE_OF_OPERATOR.clear();

	/*
	 ***************************************************************************
	 * AVM NULL / NOP STATEMENT
	 ***************************************************************************
	 */
	OPERATOR_NULL = nullptr;

	OPERATOR_NOP  = nullptr;

	/*
	 ***************************************************************************
	 * AVM META STATEMENT
	 ***************************************************************************
	 */
	OPERATOR_INFORMAL = nullptr;

	OPERATOR_TRACE = nullptr;
	OPERATOR_DEBUG = nullptr;

	OPERATOR_COMMENT = nullptr;
	OPERATOR_QUOTE   = nullptr;

	OPERATOR_META_EVAL = nullptr;
	OPERATOR_META_RUN  = nullptr;


	/*
	 ***************************************************************************
	 * AVM UFI STATEMENT
	 ***************************************************************************
	 */
	OPERATOR_UFI = nullptr;

	/*
	 ***************************************************************************
	 * AVM FORM CONSTRUCTOR STATEMENT
	 ***************************************************************************
	 */
	OPERATOR_CTOR = nullptr;

	/*
	 ***************************************************************************
	 * AVM MACHINE SELF SUPER
	 ***************************************************************************
	 */
	OPERATOR_SELF = nullptr;

	OPERATOR_SUPER = nullptr;

	/*
	 ***************************************************************************
	 * AVM MACHINE MANAGING
	 ***************************************************************************
	 */
	OPERATOR_CONTEXT_SWITCHER = nullptr;

	OPERATOR_PROCESS_STATE_GET = nullptr;
	OPERATOR_PROCESS_STATE_SET = nullptr;

	OPERATOR_INIT = nullptr;
	OPERATOR_FINAL = nullptr;
	OPERATOR_DESTROY = nullptr;

	OPERATOR_START = nullptr;
	OPERATOR_RESTART = nullptr;
	OPERATOR_STOP = nullptr;

	OPERATOR_WAIT = nullptr;

	OPERATOR_SUSPEND = nullptr;
	OPERATOR_RESUME = nullptr;

	OPERATOR_IENABLE_INVOKE = nullptr;
	OPERATOR_ENABLE_INVOKE = nullptr;
	OPERATOR_ENABLE_SET = nullptr;

	OPERATOR_IDISABLE_INVOKE = nullptr;
	OPERATOR_DISABLE_INVOKE = nullptr;
	OPERATOR_DISABLE_SET = nullptr;
	OPERATOR_DISABLE_CHILD = nullptr;
	OPERATOR_DISABLE_SELF = nullptr;
	OPERATOR_DISABLE_SELVES = nullptr;

	OPERATOR_IABORT_INVOKE = nullptr;
	OPERATOR_ABORT_INVOKE = nullptr;
	OPERATOR_ABORT_SET = nullptr;
	OPERATOR_ABORT_CHILD = nullptr;
	OPERATOR_ABORT_SELF = nullptr;
	OPERATOR_ABORT_SELVES = nullptr;

	OPERATOR_HISTORY_CLEAR = nullptr;
	OPERATOR_DEEP_HISTORY_INVOKE = nullptr;
	OPERATOR_SHALLOW_HISTORY_INVOKE = nullptr;

	OPERATOR_IRUN = nullptr;
	OPERATOR_RUN = nullptr;
	OPERATOR_RTC = nullptr;

	OPERATOR_INVOKE_NEW = nullptr;

	OPERATOR_INVOKE_ROUTINE = nullptr;

	OPERATOR_INVOKE_TRANSITION = nullptr;

	OPERATOR_INVOKE_METHOD = nullptr;
	OPERATOR_INVOKE_PROGRAM = nullptr;
	OPERATOR_INVOKE_FUNCTION = nullptr;

	OPERATOR_INVOKE_LAMBDA_APPLY = nullptr;
	OPERATOR_INVOKE_LAMBDA_LET = nullptr;

	OPERATOR_GOTO = nullptr;

	OPERATOR_SCHEDULE_INVOKE = nullptr;
	OPERATOR_SCHEDULE_GET = nullptr;
	OPERATOR_SCHEDULE_IN = nullptr;
	OPERATOR_SCHEDULE_SET = nullptr;

	OPERATOR_DEFER_INVOKE = nullptr;
	OPERATOR_DEFER_GET = nullptr;
	OPERATOR_DEFER_SET = nullptr;

	OPERATOR_FORK = nullptr;
	OPERATOR_JOIN = nullptr;

	OPERATOR_INPUT_ENABLED = nullptr;

	OPERATOR_RDV = nullptr;

	OPERATOR_SYNCHRONIZE = nullptr;

	/*
	 ***************************************************************************
	 * AVM DATA STATUS
	 ***************************************************************************
	 */

	OPERATOR_STATUS_WAS = nullptr;
	OPERATOR_STATUS_IS = nullptr;
	OPERATOR_STATUS_BEING = nullptr;
	OPERATOR_STATUS_WILL = nullptr;

	OPERATOR_CHANGED = nullptr;
	OPERATOR_CHANGED_TO = nullptr;


	/*
	 ***************************************************************************
	 * AVM PROGRAM SCHEDULING
	 ***************************************************************************
	 */
	OPERATOR_ASYNCHRONOUS = nullptr;
	OPERATOR_STRONG_SYNCHRONOUS = nullptr;
	OPERATOR_WEAK_SYNCHRONOUS = nullptr;

	OPERATOR_INTERLEAVING = nullptr;
	OPERATOR_PARTIAL_ORDER = nullptr;

	OPERATOR_PARALLEL = nullptr;

	//// Optimized version of concurrency for RDV synchronization
	OPERATOR_RDV_ASYNCHRONOUS = nullptr;
	OPERATOR_RDV_STRONG_SYNCHRONOUS = nullptr;
	OPERATOR_RDV_WEAK_SYNCHRONOUS = nullptr;

	OPERATOR_RDV_INTERLEAVING = nullptr;
	OPERATOR_RDV_PARTIAL_ORDER = nullptr;

	OPERATOR_RDV_PARALLEL = nullptr;

	OPERATOR_EXCLUSIVE = nullptr;

	OPERATOR_NONDETERMINISM = nullptr;

	OPERATOR_PRIOR_GT = nullptr;
	OPERATOR_PRIOR_LT = nullptr;

	OPERATOR_SCHEDULE_AND_THEN = nullptr;
	OPERATOR_SCHEDULE_OR_ELSE = nullptr;

	OPERATOR_ATOMIC_SEQUENCE = nullptr;

	OPERATOR_SEQUENCE = nullptr;
	OPERATOR_SEQUENCE_SIDE = nullptr;
	OPERATOR_SEQUENCE_WEAK = nullptr;

	OPERATOR_PRODUCT = nullptr;

	/*
	 ***************************************************************************
	 * AVM BUFFER MANAGING
	 ***************************************************************************
	 */
	OPERATOR_UPDATE_BUFFER = nullptr;

	/*
	 ************************** *************************************************
	 * LAMBDA STATEMENT
	 ***************************************************************************
	 */
	OPERATOR_APPLY  = nullptr;
	OPERATOR_LAMBDA = nullptr;

	/*
	 ***************************************************************************
	 * LET STATEMENT
	 ***************************************************************************
	 */
	OPERATOR_LET = nullptr;

	/*
	 ***************************************************************************
	 * LOOKUP STATEMENT
	 ***************************************************************************
	 */
	OPERATOR_LOOKUP_INT_EXT = nullptr;
	OPERATOR_LOOKUP_INT = nullptr;
	OPERATOR_LOOKUP_NEAREST = nullptr;
	OPERATOR_LOOKUP_BELOW = nullptr;
	OPERATOR_LOOKUP_ABOVE = nullptr;
	OPERATOR_LOOKUP2D_INT_EXT = nullptr;

	/*
	 ***************************************************************************
	 * AVM PRIMITIVE STATEMENT
	 ***************************************************************************
	 */
	OPERATOR_ASSIGN = nullptr;
	OPERATOR_ASSIGN_AFTER = nullptr;
	OPERATOR_ASSIGN_OP = nullptr;
	OPERATOR_ASSIGN_OP_AFTER = nullptr;
	OPERATOR_ASSIGN_REF = nullptr;
	OPERATOR_ASSIGN_MACRO = nullptr;

	OPERATOR_ASSIGN_NEWFRESH = nullptr;
	OPERATOR_ASSIGN_RESET    = nullptr;

	OPERATOR_GUARD       = nullptr;
	OPERATOR_TIMED_GUARD = nullptr;

	OPERATOR_EVENT = nullptr;

	OPERATOR_CHECK_SAT = nullptr;


	OPERATOR_INPUT = nullptr;
	OPERATOR_INPUT_FROM = nullptr;

	OPERATOR_INPUT_SAVE = nullptr;

	OPERATOR_INPUT_VAR = nullptr;
	OPERATOR_INPUT_FLOW = nullptr;

	OPERATOR_INPUT_ENV       = nullptr;
	OPERATOR_INPUT_BUFFER    = nullptr;
	OPERATOR_INPUT_RDV       = nullptr;
	OPERATOR_INPUT_BROADCAST = nullptr;
	OPERATOR_INPUT_DELEGATE  = nullptr;


	OPERATOR_OUTPUT    = nullptr;
	OPERATOR_OUTPUT_TO = nullptr;

	OPERATOR_OUTPUT_VAR  = nullptr;
	OPERATOR_OUTPUT_FLOW = nullptr;

	OPERATOR_OUTPUT_ENV       = nullptr;
	OPERATOR_OUTPUT_BUFFER    = nullptr;
	OPERATOR_OUTPUT_RDV       = nullptr;
	OPERATOR_OUTPUT_BROADCAST = nullptr;
	OPERATOR_OUTPUT_DELEGATE  = nullptr;


	OPERATOR_PRESENT = nullptr;
	OPERATOR_ABSENT  = nullptr;


	OPERATOR_IF  = nullptr;
	OPERATOR_IFE = nullptr;

	OPERATOR_FOR     = nullptr;
	OPERATOR_FOREACH = nullptr;

	OPERATOR_WHILE_DO = nullptr;
	OPERATOR_DO_WHILE = nullptr;

	OPERATOR_BREAK    = nullptr;
	OPERATOR_CONTINUE = nullptr;
	OPERATOR_RETURN   = nullptr;

	OPERATOR_EXIT = nullptr;

	OPERATOR_STEP_MARK = nullptr;


	/*
	 ***************************************************************************
	 * AVM PREDICAT EXPRESSION
	 ***************************************************************************
	 */
	OPERATOR_EXISTS = nullptr;
	OPERATOR_FORALL = nullptr;

	OPERATOR_NOT = nullptr;

	OPERATOR_AND  = nullptr;
	OPERATOR_AND_THEN = nullptr;
	OPERATOR_NAND = nullptr;
	OPERATOR_XAND = nullptr;

	OPERATOR_OR   = nullptr;
	OPERATOR_OR_ELSE = nullptr;
	OPERATOR_NOR  = nullptr;
	OPERATOR_XOR  = nullptr;
	OPERATOR_XNOR = nullptr;

	OPERATOR_IMPLIES = nullptr;


	/*
	 ***************************************************************************
	 * AVM COMPARISON EXPRESSION
	 ***************************************************************************
	 */
	OPERATOR_SEQ  = nullptr;
	OPERATOR_NSEQ = nullptr;


	/*
	 ***************************************************************************
	 * AVM COMPARISON EXPRESSION
	 ***************************************************************************
	 */
	OPERATOR_EQ  = nullptr;
	OPERATOR_NEQ = nullptr;

	OPERATOR_LT  = nullptr;
	OPERATOR_LTE = nullptr;

	OPERATOR_GT  = nullptr;
	OPERATOR_GTE = nullptr;

	/*
	 ***************************************************************************
	 * AVM BITWISE EXPRESSION
	 ***************************************************************************
	 */
	OPERATOR_BNOT = nullptr;
	OPERATOR_BAND = nullptr;

	OPERATOR_BOR  = nullptr;
	OPERATOR_BXOR = nullptr;

	OPERATOR_LSHIFT = nullptr;
	OPERATOR_RSHIFT = nullptr;


	/*
	 ***************************************************************************
	 * AVM ARITHMETIC EXPRESSION
	 ***************************************************************************
	 */
	OPERATOR_PLUS = nullptr;

	OPERATOR_MINUS = nullptr;
	OPERATOR_UMINUS = nullptr;

	OPERATOR_MULT = nullptr;

	OPERATOR_POW = nullptr;

	OPERATOR_DIV = nullptr;

	OPERATOR_MOD = nullptr;

	OPERATOR_MIN = nullptr;
	OPERATOR_MAX = nullptr;


	/*
	 ***************************************************************************
	 * AVM MATHEMATICAL FUNCTION
	 ***************************************************************************
	 */

	//// RANDOM
	OPERATOR_RANDOM = nullptr;

	//// ROUNDING
	OPERATOR_ABS   = nullptr;
	OPERATOR_CEIL  = nullptr;
	OPERATOR_FLOOR = nullptr;
	OPERATOR_ROUND = nullptr;

	OPERATOR_TRUNCATE = nullptr;


	//// EXP - LOG
	OPERATOR_SQRT = nullptr;

	OPERATOR_EXP = nullptr;
	OPERATOR_LN  = nullptr;
	OPERATOR_LOG = nullptr;


	//// TRIGONOMETRIC
	OPERATOR_SIN = nullptr;
	OPERATOR_COS = nullptr;
	OPERATOR_TAN = nullptr;

	OPERATOR_SINH = nullptr;
	OPERATOR_COSH = nullptr;
	OPERATOR_TANH = nullptr;

	OPERATOR_ASIN = nullptr;
	OPERATOR_ACOS = nullptr;
	OPERATOR_ATAN = nullptr;
	OPERATOR_ATAN2 = nullptr;

	OPERATOR_ASINH = nullptr;
	OPERATOR_ACOSH = nullptr;
	OPERATOR_ATANH = nullptr;

	/*
	 ***************************************************************************
	 * AVM STRING // COLLECTION OPERATOR
	 ***************************************************************************
	 */
	OPERATOR_CONTAINS = nullptr;

	OPERATOR_IN    = nullptr;
	OPERATOR_NOTIN = nullptr;

	OPERATOR_SUBSET   = nullptr;
	OPERATOR_SUBSETEQ = nullptr;

	OPERATOR_INTERSECT = nullptr;

	OPERATOR_STARTS_WITH = nullptr;
	OPERATOR_ENDS_WITH   = nullptr;

	OPERATOR_CONCAT = nullptr;
	OPERATOR_APPEND = nullptr;

	OPERATOR_REMOVE = nullptr;
	OPERATOR_CLEAR  = nullptr;
	OPERATOR_RESIZE = nullptr;
	OPERATOR_SELECT = nullptr;

	OPERATOR_PUSH = nullptr;
	OPERATOR_ASSIGN_TOP = nullptr;
	OPERATOR_TOP = nullptr;
	OPERATOR_POP = nullptr;
	OPERATOR_POP_FROM = nullptr;

	OPERATOR_EMPTY    = nullptr;
	OPERATOR_NONEMPTY = nullptr;

	OPERATOR_SINGLETON = nullptr;
	OPERATOR_POPULATED = nullptr;

	OPERATOR_FULL = nullptr;

	OPERATOR_SIZE = nullptr;

	/*
	 ***************************************************************************
	 * IOLTL BEHAVIORAL PREDICAT
	 ***************************************************************************
	 */
	OPERATOR_GLOBALLY    = nullptr;
	OPERATOR_UNTIL      = nullptr;
	OPERATOR_NEXT       = nullptr;
	OPERATOR_EVENTUALLY = nullptr;
	OPERATOR_RELEASES   = nullptr;
	OPERATOR_OBS        = nullptr;

	/*
	 ***************************************************************************
	 * IOLTL LOGICAL PREDICAT
	 ***************************************************************************
	 */
	OPERATOR_AND_T = nullptr;
	OPERATOR_OR_T  = nullptr;
	OPERATOR_NOT_T = nullptr;
	OPERATOR_IMP_T = nullptr;
//	*/
}


/**
 * Operator
 */
Operator * OperatorManager::newOperator(
		AVM_OPCODE anAvmOpCode, AVM_OPCODE anOptimizedOpCode,
		const std::string & aFullyQualifiedNameID, const std::string & aNameID,
		ALGEBRA_QUALIFIER anAlgebraQualifier, FIX_NOTATION aFixQualifier,
		const std::string & aStandardSymbol, const std::string & aSyntaxMIXFIX,
		const std::string & aSymbolQEPCAD)
{
	Operator * theNewOperator( new Operator(aFullyQualifiedNameID, aNameID,
			anAvmOpCode, anOptimizedOpCode, anAlgebraQualifier, aFixQualifier,
			aStandardSymbol, aSyntaxMIXFIX, aSymbolQEPCAD) );

	registerOp( theNewOperator );

	return( theNewOperator );
}



/**
 * TESTER
 */

bool OperatorManager::isQuote(const Operator * anOperator)
{
	switch( anOperator->getAvmOpCode() )
	{
		case AVM_OPCODE_QUOTE:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}

bool OperatorManager::isMeta(const Operator * anOperator)
{
	switch( anOperator->getAvmOpCode() )
	{
		case AVM_OPCODE_META_EVAL:
		case AVM_OPCODE_META_RUN:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}

bool OperatorManager::isMetaEval(const Operator * anOperator)
{
	switch( anOperator->getAvmOpCode() )
	{
		case AVM_OPCODE_META_EVAL:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}

bool OperatorManager::isMetaRun(const Operator * anOperator)
{
	switch( anOperator->getAvmOpCode() )
	{
		case AVM_OPCODE_META_RUN:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}

bool OperatorManager::isAssignBinary(const Operator * anOperator)
{
	switch( anOperator->getAvmOpCode() )
	{
		case AVM_OPCODE_ASSIGN:
		case AVM_OPCODE_ASSIGN_AFTER:
		case AVM_OPCODE_ASSIGN_OP_AFTER:
		case AVM_OPCODE_ASSIGN_REF:
		case AVM_OPCODE_ASSIGN_MACRO:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}

bool OperatorManager::isAssignUnary(const Operator * anOperator)
{
	switch( anOperator->getAvmOpCode() )
	{
		case AVM_OPCODE_ASSIGN_NEWFRESH:
		case AVM_OPCODE_ASSIGN_RESET:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}


bool OperatorManager::isUfi(const Operator * anOperator)
{
	switch( anOperator->getAvmOpCode() )
	{
		case AVM_OPCODE_UFI:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}

bool OperatorManager::isCtor(const Operator * anOperator)
{
	switch( anOperator->getAvmOpCode() )
	{
		case AVM_OPCODE_CTOR:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}


bool OperatorManager::isUfiOrCtor(const Operator * anOperator)
{
	switch( anOperator->getAvmOpCode() )
	{
		case AVM_OPCODE_UFI:
		case AVM_OPCODE_CTOR:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}

bool OperatorManager::isNewfresh(const Operator * anOperator)
{
	switch( anOperator->getAvmOpCode() )
	{
		case AVM_OPCODE_ASSIGN_NEWFRESH:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}



bool OperatorManager::isSequence(const Operator * anOperator)
{
	switch( anOperator->getAvmOpCode() )
	{
		case AVM_OPCODE_ATOMIC_SEQUENCE:

		case AVM_OPCODE_SEQUENCE:
		case AVM_OPCODE_SEQUENCE_SIDE:
		case AVM_OPCODE_SEQUENCE_WEAK:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}


bool OperatorManager::isSchedule(const Operator * anOperator)
{
	switch( anOperator->getAvmOpCode() )
	{
		/*
		 ***************************************************************************
		 * AVM PROGRAM SCHEDULING
		 ***************************************************************************
		 */
		case AVM_OPCODE_ATOMIC_SEQUENCE:

		case AVM_OPCODE_SEQUENCE:
		case AVM_OPCODE_SEQUENCE_SIDE:
		case AVM_OPCODE_SEQUENCE_WEAK:

		case AVM_OPCODE_INPUT_ENABLED:

		case AVM_OPCODE_ASYNCHRONOUS:
		case AVM_OPCODE_STRONG_SYNCHRONOUS:
		case AVM_OPCODE_WEAK_SYNCHRONOUS:
		case AVM_OPCODE_INTERLEAVING:
		case AVM_OPCODE_PARTIAL_ORDER:
		case AVM_OPCODE_PARALLEL:

		case AVM_OPCODE_EXCLUSIVE:
		case AVM_OPCODE_NONDETERMINISM:

		case AVM_OPCODE_PRIOR_GT:
		case AVM_OPCODE_PRIOR_LT:

		case AVM_OPCODE_SCHEDULE_AND_THEN:
		case AVM_OPCODE_SCHEDULE_OR_ELSE:

		case AVM_OPCODE_FORK:

		case AVM_OPCODE_PRODUCT:

		case AVM_OPCODE_CONTEXT_SWITCHER:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}

bool OperatorManager::isMachine(const Operator * anOperator)
{
	switch( anOperator->getAvmOpCode() )
	{
		/*
		 ***************************************************************************
		 * AVM MACHINE ACTIVITY
		 ***************************************************************************
		 */
		case AVM_OPCODE_SELF:
		case AVM_OPCODE_SUPER:

		case AVM_OPCODE_SCHEDULE_GET:

		case AVM_OPCODE_INVOKE_NEW:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}


bool OperatorManager::isActivity(const Operator * anOperator)
{
	switch( anOperator->getAvmOpCode() )
	{
		/*
		 ***************************************************************************
		 * AVM PROGRAM ACTIVITY
		 ***************************************************************************
		 */
		case AVM_OPCODE_PROCESS_STATE_SET:

		case AVM_OPCODE_INIT:
		case AVM_OPCODE_FINAL:
		case AVM_OPCODE_DESTROY:

		case AVM_OPCODE_START:
		case AVM_OPCODE_RESTART:
		case AVM_OPCODE_STOP:

		case AVM_OPCODE_WAIT:

		case AVM_OPCODE_SUSPEND:
		case AVM_OPCODE_RESUME:

		case AVM_OPCODE_IENABLE_INVOKE:
		case AVM_OPCODE_ENABLE_INVOKE:
		case AVM_OPCODE_ENABLE_SET:

		case AVM_OPCODE_IDISABLE_INVOKE:
		case AVM_OPCODE_DISABLE_INVOKE:
		case AVM_OPCODE_DISABLE_SET:

		case AVM_OPCODE_DISABLE_CHILD:
		case AVM_OPCODE_DISABLE_SELF:
		case AVM_OPCODE_DISABLE_SELVES:

		case AVM_OPCODE_IABORT_INVOKE:
		case AVM_OPCODE_ABORT_INVOKE:
		case AVM_OPCODE_ABORT_SET:

		case AVM_OPCODE_ABORT_CHILD:
		case AVM_OPCODE_ABORT_SELF:
		case AVM_OPCODE_ABORT_SELVES:

		case AVM_OPCODE_IRUN:
		case AVM_OPCODE_RUN:

		case AVM_OPCODE_RTC:

		case AVM_OPCODE_SCHEDULE_INVOKE:

		case AVM_OPCODE_DEFER_INVOKE:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}


bool OperatorManager::isScheduledActivity(const Operator * anOperator)
{
	switch( anOperator->getAvmOpCode() )
	{
		/*
		 ***************************************************************************
		 * AVM PROGRAM ACTIVITY
		 ***************************************************************************
		 */
		case AVM_OPCODE_INIT:
		case AVM_OPCODE_FINAL:
		case AVM_OPCODE_DESTROY:

		case AVM_OPCODE_START:
		case AVM_OPCODE_RESTART:
		case AVM_OPCODE_STOP:

		case AVM_OPCODE_WAIT:

		case AVM_OPCODE_SUSPEND:
		case AVM_OPCODE_RESUME:

		case AVM_OPCODE_IRUN:
		case AVM_OPCODE_RUN:

		case AVM_OPCODE_RTC:

		case AVM_OPCODE_SCHEDULE_INVOKE:

		case AVM_OPCODE_DEFER_INVOKE:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}


bool OperatorManager::isInput(const Operator * anOperator)
{
	switch( anOperator->getAvmOpCode() )
	{
		/*
		 ***************************************************************************
		 * AVM PROGRAM INPUT
		 ***************************************************************************
		 */
		case AVM_OPCODE_INPUT:
		case AVM_OPCODE_INPUT_FROM:

		case AVM_OPCODE_INPUT_SAVE:

		case AVM_OPCODE_INPUT_ENV:
		case AVM_OPCODE_INPUT_VAR:
		case AVM_OPCODE_INPUT_FLOW:
		case AVM_OPCODE_INPUT_BUFFER:
		case AVM_OPCODE_INPUT_BROADCAST:

		case AVM_OPCODE_INPUT_RDV:
		case AVM_OPCODE_INPUT_MULTI_RDV:

		case AVM_OPCODE_INPUT_DELEGATE:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}


bool OperatorManager::isOutput(const Operator * anOperator)
{
	switch( anOperator->getAvmOpCode() )
	{
		/*
		 ***************************************************************************
		 * AVM PROGRAM OUTPUT
		 ***************************************************************************
		 */
		case AVM_OPCODE_OUTPUT:
		case AVM_OPCODE_OUTPUT_TO:

		case AVM_OPCODE_OUTPUT_ENV:
		case AVM_OPCODE_OUTPUT_VAR:
		case AVM_OPCODE_OUTPUT_FLOW:
		case AVM_OPCODE_OUTPUT_BUFFER:
		case AVM_OPCODE_OUTPUT_BROADCAST:

		case AVM_OPCODE_OUTPUT_RDV:
		case AVM_OPCODE_OUTPUT_MULTI_RDV:

		case AVM_OPCODE_OUTPUT_DELEGATE:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}


bool OperatorManager::isArithmetic(const Operator * anOperator)
{
	switch( anOperator->getAvmOpCode() )
	{
		/*
		 ***********************************************************************
		 * AVM ARITHMETIC EXPRESSION
		 ***********************************************************************
		 */

		case AVM_OPCODE_PLUS:
		case AVM_OPCODE_MINUS:
		case AVM_OPCODE_UMINUS:

		case AVM_OPCODE_MULT:
		case AVM_OPCODE_POW:

		case AVM_OPCODE_DIV:
		case AVM_OPCODE_MOD:

		case AVM_OPCODE_BNOT:
		case AVM_OPCODE_BAND:
		case AVM_OPCODE_BOR:
		case AVM_OPCODE_BXOR:
		case AVM_OPCODE_LSHIFT:
		case AVM_OPCODE_RSHIFT:

		case AVM_OPCODE_RANDOM:

		case AVM_OPCODE_ABS:
		case AVM_OPCODE_CEIL:
		case AVM_OPCODE_FLOOR:
		case AVM_OPCODE_ROUND:
		case AVM_OPCODE_TRUNCATE:

		case AVM_OPCODE_SQRT:
		case AVM_OPCODE_EXP:
		case AVM_OPCODE_LN:
		case AVM_OPCODE_LOG:

		case AVM_OPCODE_SIN:
		case AVM_OPCODE_COS:
		case AVM_OPCODE_TAN:

		case AVM_OPCODE_SINH:
		case AVM_OPCODE_COSH:
		case AVM_OPCODE_TANH:

		case AVM_OPCODE_ASIN:
		case AVM_OPCODE_ACOS:
		case AVM_OPCODE_ATAN:
		case AVM_OPCODE_ATAN2:

		case AVM_OPCODE_ASINH:
		case AVM_OPCODE_ACOSH:
		case AVM_OPCODE_ATANH:

		case AVM_OPCODE_MAX:
		case AVM_OPCODE_MIN:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}


bool OperatorManager::isRelational(const Operator * anOperator)
{
	switch( anOperator->getAvmOpCode() )
	{
		/*
		 ***********************************************************************
		 * AVM RELATIONAL EXPRESSION
		 ***********************************************************************
		 */

		case AVM_OPCODE_EQ:
		case AVM_OPCODE_NEQ:

		case AVM_OPCODE_SEQ:
		case AVM_OPCODE_NSEQ:

		case AVM_OPCODE_LT:
		case AVM_OPCODE_LTE:
		case AVM_OPCODE_GT:
		case AVM_OPCODE_GTE:

		case AVM_OPCODE_EMPTY:
		case AVM_OPCODE_NONEMPTY:
		case AVM_OPCODE_SINGLETON:
		case AVM_OPCODE_POPULATED:
		case AVM_OPCODE_FULL:

		case AVM_OPCODE_IN:
		case AVM_OPCODE_NOTIN:
		case AVM_OPCODE_CONTAINS:

		case AVM_OPCODE_SUBSET:
		case AVM_OPCODE_SUBSETEQ:

		case AVM_OPCODE_INTERSECT:

		case AVM_OPCODE_STARTS_WITH:
		case AVM_OPCODE_ENDS_WITH:


		case AVM_OPCODE_PRESENT:
		case AVM_OPCODE_ABSENT:


		case AVM_OPCODE_SCHEDULE_IN:

		case AVM_OPCODE_STATUS_BEING:
		case AVM_OPCODE_STATUS_IS:
		case AVM_OPCODE_STATUS_WAS:
		case AVM_OPCODE_STATUS_WILL:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}


bool OperatorManager::isPropositional(const Operator * anOperator)
{
	switch( anOperator->getAvmOpCode() )
	{
		/*
		 ***********************************************************************
		 * AVM PROPOSITIONAL EXPRESSION
		 ***********************************************************************
		 */
		case AVM_OPCODE_EXISTS:
		case AVM_OPCODE_FORALL:

		case AVM_OPCODE_NOT:

		case AVM_OPCODE_AND:
		case AVM_OPCODE_NAND:

		case AVM_OPCODE_XAND:

		case AVM_OPCODE_OR:
		case AVM_OPCODE_NOR:

		case AVM_OPCODE_XOR:
		case AVM_OPCODE_XNOR:

		case AVM_OPCODE_IMPLIES:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}


bool OperatorManager::isQuantifier(const Operator * anOperator)
{
	switch( anOperator->getAvmOpCode() )
	{
		/*
		 ***********************************************************************
		 * AVM QUANTIFIED EXPRESSION
		 ***********************************************************************
		 */
		case AVM_OPCODE_EXISTS:
		case AVM_OPCODE_FORALL:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}



bool OperatorManager::isTemporalLogic(const Operator * anOperator)
{
	switch( anOperator->getAvmOpCode() )
	{
		/*
		 ***********************************************************************
		 * IOLTL STATEMENT
		 ***********************************************************************
		 */
		case AVM_OPCODE_GLOBALLY:
		case AVM_OPCODE_UNTIL:
		case AVM_OPCODE_NEXT:
		case AVM_OPCODE_EVENTUALLY:
		case AVM_OPCODE_RELEASES:
		case AVM_OPCODE_OBS:

		case AVM_OPCODE_AND_T:
		case AVM_OPCODE_OR_T:
		case AVM_OPCODE_NOT_T:
		case AVM_OPCODE_IMP_T:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}



bool OperatorManager::isConditionnal(const Operator * anOperator)
{
	switch( anOperator->getAvmOpCode() )
	{
		case AVM_OPCODE_IF:
		case AVM_OPCODE_IFE:

		case AVM_OPCODE_AND_THEN:
		case AVM_OPCODE_OR_ELSE:

		case AVM_OPCODE_FOR:
		case AVM_OPCODE_FOREACH:
		case AVM_OPCODE_WHILE_DO:
		case AVM_OPCODE_DO_WHILE:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}



bool OperatorManager::isStatement(const Operator * anOperator)
{
	switch( anOperator->getAvmOpCode() )
	{
		/*
		 ***********************************************************************
		 * AVM NOP STATEMENT
		 ***********************************************************************
		 */
		case AVM_OPCODE_NOP:


		/*
		 ***********************************************************************
		 * AVM MACHINE ACTIVITY
		 ***********************************************************************
		 */
		case AVM_OPCODE_CONTEXT_SWITCHER:

		case AVM_OPCODE_PROCESS_STATE_GET:
		case AVM_OPCODE_PROCESS_STATE_SET:

		case AVM_OPCODE_INIT:
		case AVM_OPCODE_FINAL:
		case AVM_OPCODE_DESTROY:

		case AVM_OPCODE_START:
		case AVM_OPCODE_RESTART:
		case AVM_OPCODE_STOP:

		case AVM_OPCODE_WAIT:

		case AVM_OPCODE_SUSPEND:
		case AVM_OPCODE_RESUME:

		case AVM_OPCODE_IENABLE_INVOKE:
		case AVM_OPCODE_ENABLE_INVOKE:
		case AVM_OPCODE_ENABLE_SET:

		case AVM_OPCODE_IDISABLE_INVOKE:
		case AVM_OPCODE_DISABLE_INVOKE:
		case AVM_OPCODE_DISABLE_SET:

		case AVM_OPCODE_DISABLE_CHILD:
		case AVM_OPCODE_DISABLE_SELF:
		case AVM_OPCODE_DISABLE_SELVES:

		case AVM_OPCODE_IABORT_INVOKE:
		case AVM_OPCODE_ABORT_INVOKE:
		case AVM_OPCODE_ABORT_SET:

		case AVM_OPCODE_ABORT_CHILD:
		case AVM_OPCODE_ABORT_SELF:
		case AVM_OPCODE_ABORT_SELVES:

		case AVM_OPCODE_HISTORY_CLEAR:
		case AVM_OPCODE_DEEP_HISTORY_INVOKE:
		case AVM_OPCODE_SHALLOW_HISTORY_INVOKE:

		case AVM_OPCODE_IRUN:
		case AVM_OPCODE_RUN:

		case AVM_OPCODE_RTC:

		case AVM_OPCODE_SCHEDULE_INVOKE:
		case AVM_OPCODE_SCHEDULE_GET:
		case AVM_OPCODE_SCHEDULE_SET:

		case AVM_OPCODE_DEFER_INVOKE:
		case AVM_OPCODE_DEFER_GET:
		case AVM_OPCODE_DEFER_SET:

		case AVM_OPCODE_FORK:

		case AVM_OPCODE_JOIN:

		case AVM_OPCODE_RDV:

		case AVM_OPCODE_INPUT_ENABLED:

		case AVM_OPCODE_SYNCHRONIZE:


		case AVM_OPCODE_INVOKE_NEW:

		case AVM_OPCODE_SELF:
		case AVM_OPCODE_SUPER:


		/*
		 ***********************************************************************
		 * AVM MACHINE STATUS
		 ***********************************************************************
		 */
		case AVM_OPCODE_STATUS_BEING:
		case AVM_OPCODE_STATUS_IS:
		case AVM_OPCODE_STATUS_WAS:
		case AVM_OPCODE_STATUS_WILL:


		/*
		 ***********************************************************************
		 * AVM PROGRAM SCHEDULING
		 ***********************************************************************
		 */
		case AVM_OPCODE_ASYNCHRONOUS:
		case AVM_OPCODE_STRONG_SYNCHRONOUS:
		case AVM_OPCODE_WEAK_SYNCHRONOUS:
		case AVM_OPCODE_INTERLEAVING:
		case AVM_OPCODE_PARTIAL_ORDER:
		case AVM_OPCODE_PARALLEL:

		case AVM_OPCODE_EXCLUSIVE:

		case AVM_OPCODE_NONDETERMINISM:


		case AVM_OPCODE_PRIOR_GT:
		case AVM_OPCODE_PRIOR_LT:

		case AVM_OPCODE_ATOMIC_SEQUENCE:

		case AVM_OPCODE_SEQUENCE:
		case AVM_OPCODE_SEQUENCE_SIDE:
		case AVM_OPCODE_SEQUENCE_WEAK:


		case AVM_OPCODE_PRODUCT:


		/*
		 ***********************************************************************
		 * AVM BUFFER MANAGING
		 ***********************************************************************
		 */
		case AVM_OPCODE_UPDATE_BUFFER:


		/*
		 ***********************************************************************
		 * LAMBDA STATEMENT
		 ***********************************************************************
		 */
		case AVM_OPCODE_APPLY:

		case AVM_OPCODE_LAMBDA:

		case AVM_OPCODE_INVOKE_ROUTINE:

		case AVM_OPCODE_INVOKE_TRANSITION:

		case AVM_OPCODE_INVOKE_METHOD:
		case AVM_OPCODE_INVOKE_PROGRAM:
		case AVM_OPCODE_INVOKE_FUNCTION:

		case AVM_OPCODE_INVOKE_LAMBDA_APPLY:
		case AVM_OPCODE_INVOKE_LAMBDA_LET:


		/*
		 ***********************************************************************
		 * LET STATEMENT
		 ***********************************************************************
		 */
		case AVM_OPCODE_LET:


		/*
		 ***********************************************************************
		 * AVM PRIMITIVE STATEMENT
		 ***********************************************************************
		 */
		case AVM_OPCODE_ASSIGN:
		case AVM_OPCODE_ASSIGN_AFTER:
		case AVM_OPCODE_ASSIGN_OP_AFTER:
		case AVM_OPCODE_ASSIGN_REF:
		case AVM_OPCODE_ASSIGN_MACRO:

		case AVM_OPCODE_ASSIGN_NEWFRESH:
		case AVM_OPCODE_ASSIGN_RESET:

		case AVM_OPCODE_GUARD:

		case AVM_OPCODE_CHECK_SAT:

		case AVM_OPCODE_INPUT:
		case AVM_OPCODE_INPUT_FROM:

		case AVM_OPCODE_INPUT_SAVE:

		case AVM_OPCODE_OUTPUT:
		case AVM_OPCODE_OUTPUT_TO:

		case AVM_OPCODE_PRESENT:
		case AVM_OPCODE_ABSENT:

		case AVM_OPCODE_IF:
		case AVM_OPCODE_IFE:

		case AVM_OPCODE_FOR:
		case AVM_OPCODE_FOREACH:
		case AVM_OPCODE_WHILE_DO:
		case AVM_OPCODE_DO_WHILE:

		case AVM_OPCODE_BREAK:
		case AVM_OPCODE_CONTINUE:
		case AVM_OPCODE_RETURN:
		case AVM_OPCODE_EXIT:

		case AVM_OPCODE_STEP_MARK:

		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}


bool OperatorManager::isAtomicStatement(const Operator * anOperator)
{
	switch( anOperator->getOptimizedOpCode() )
	{
		case AVM_OPCODE_NOP:
		case AVM_OPCODE_COMMENT:
		case AVM_OPCODE_INFORMAL:
		case AVM_OPCODE_QUOTE:
		case AVM_OPCODE_TRACE:

		case AVM_OPCODE_ASSIGN:
		case AVM_OPCODE_ASSIGN_AFTER:
		case AVM_OPCODE_ASSIGN_OP_AFTER:
		case AVM_OPCODE_ASSIGN_REF:
		case AVM_OPCODE_ASSIGN_MACRO:

		case AVM_OPCODE_ASSIGN_NEWFRESH:

		case AVM_OPCODE_ASSIGN_RESET:

		case AVM_OPCODE_GUARD:
		case AVM_OPCODE_TIMED_GUARD:

		case AVM_OPCODE_EVENT:

		case AVM_OPCODE_CHECK_SAT:

		case AVM_OPCODE_PROCESS_STATE_GET:
//		case AVM_OPCODE_PROCESS_STATE_SET:

		case AVM_OPCODE_IENABLE_INVOKE:
		case AVM_OPCODE_ENABLE_INVOKE:
		case AVM_OPCODE_ENABLE_SET:

		case AVM_OPCODE_IDISABLE_INVOKE:
		case AVM_OPCODE_DISABLE_INVOKE:
		case AVM_OPCODE_DISABLE_SET:
		case AVM_OPCODE_DISABLE_CHILD:
		case AVM_OPCODE_DISABLE_SELF:
		case AVM_OPCODE_DISABLE_SELVES:

		case AVM_OPCODE_IABORT_INVOKE:
		case AVM_OPCODE_ABORT_INVOKE:
		case AVM_OPCODE_ABORT_SET:
		case AVM_OPCODE_ABORT_CHILD:
		case AVM_OPCODE_ABORT_SELF:
		case AVM_OPCODE_ABORT_SELVES:

// These statement is not atomic statement
//		case AVM_OPCODE_INPUT:
//		case AVM_OPCODE_INPUT_FROM:
//		case AVM_OPCODE_INPUT_SAVE:

		case AVM_OPCODE_INPUT_ENV:
		case AVM_OPCODE_INPUT_VAR:
		case AVM_OPCODE_INPUT_FLOW:
		case AVM_OPCODE_INPUT_BUFFER:
		case AVM_OPCODE_INPUT_BROADCAST:

// These statement is not atomic statement
//		case AVM_OPCODE_INPUT_RDV:
//		case AVM_OPCODE_INPUT_MULTI_RDV:
//		case AVM_OPCODE_INPUT_DELEGATE:

//		case AVM_OPCODE_OUTPUT:
//		case AVM_OPCODE_OUTPUT_TO:

		case AVM_OPCODE_OUTPUT_ENV:
		case AVM_OPCODE_OUTPUT_VAR:
		case AVM_OPCODE_OUTPUT_FLOW:
		case AVM_OPCODE_OUTPUT_BUFFER:
		case AVM_OPCODE_OUTPUT_BROADCAST:

//		case AVM_OPCODE_OUTPUT_RDV:
//		case AVM_OPCODE_OUTPUT_MULTI_RDV:
//		case AVM_OPCODE_OUTPUT_DELEGATE:

		case AVM_OPCODE_PRESENT:
		case AVM_OPCODE_ABSENT:


		case AVM_OPCODE_CONCAT:

		case AVM_OPCODE_REMOVE:
		case AVM_OPCODE_CLEAR:

		case AVM_OPCODE_RESIZE:

		case AVM_OPCODE_SELECT:

		case AVM_OPCODE_PUSH:
		case AVM_OPCODE_POP:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}



bool OperatorManager::isCharacter(const Operator * anOperator)
{
	switch( anOperator->getAvmOpCode() )
	{
//		case AVM_OPCODE_UNICODE:
//		{
//			return( true );
//		}

		default:
		{
			return( false );
		}
	}
}


bool OperatorManager::isString(const Operator * anOperator)
{
	switch( anOperator->getAvmOpCode() )
	{
		case AVM_OPCODE_CONCAT:
		case AVM_OPCODE_PLUS:
		case AVM_OPCODE_REMOVE:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}


bool OperatorManager::isLookup(const Operator * anOperator)
{
	switch( anOperator->getAvmOpCode() )
	{
		/*
		 ***********************************************************************
		 * AVM LOOKUP EXPRESSION
		 ***********************************************************************
		 */

		case AVM_OPCODE_LOOKUP_INT_EXT:
		case AVM_OPCODE_LOOKUP_INT:
		case AVM_OPCODE_LOOKUP_NEAREST:
		case AVM_OPCODE_LOOKUP_BELOW:
		case AVM_OPCODE_LOOKUP_ABOVE:
		case AVM_OPCODE_LOOKUP2D_INT_EXT:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}

bool OperatorManager::isLookup1D(const Operator * anOperator)
{
	switch( anOperator->getAvmOpCode() )
	{
		/*
		 ***********************************************************************
		 * AVM LOOKUP1D EXPRESSION
		 ***********************************************************************
		 */

		case AVM_OPCODE_LOOKUP_INT_EXT:
		case AVM_OPCODE_LOOKUP_INT:
		case AVM_OPCODE_LOOKUP_NEAREST:
		case AVM_OPCODE_LOOKUP_BELOW:
		case AVM_OPCODE_LOOKUP_ABOVE:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}

bool OperatorManager::isLookup2D(const Operator * anOperator)
{
	if( anOperator->isOpCode( AVM_OPCODE_LOOKUP2D_INT_EXT ) )
	{
		return( true );
	}
	else
	{
		return( false );
	}
}


bool OperatorManager::isContainerElementAccess(const Operator * anOperator)
{
	switch( anOperator->getAvmOpCode() )
	{
		case AVM_OPCODE_TOP:
		case AVM_OPCODE_POP:
		case AVM_OPCODE_POP_FROM:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}


bool OperatorManager::isContainerOperation(const Operator * anOperator)
{
	switch( anOperator->getAvmOpCode() )
	{
		case AVM_OPCODE_APPEND:
		case AVM_OPCODE_REMOVE:
		case AVM_OPCODE_CLEAR:
		case AVM_OPCODE_RESIZE:

		case AVM_OPCODE_SELECT:

		case AVM_OPCODE_INTERSECT:
		case AVM_OPCODE_CONCAT
		:
		case AVM_OPCODE_PUSH:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}


/**
 * Codomain of function
 */
bool OperatorManager::isCodomainBoolean(const Operator * anOperator)
{
	switch( anOperator->getAvmOpCode() )
	{
		default:
		{
			return( false );
		}
	}
}

bool OperatorManager::isCodomainCharacter(const Operator * anOperator)
{
	switch( anOperator->getAvmOpCode() )
	{
		default:
		{
			return( false );
		}
	}
}

bool OperatorManager::isCodomainString(const Operator * anOperator)
{
	switch( anOperator->getAvmOpCode() )
	{
		default:
		{
			return( false );
		}
	}
}

bool OperatorManager::isCodomainInteger(const Operator * anOperator)
{
	switch( anOperator->getAvmOpCode() )
	{
		case AVM_OPCODE_SIZE:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}

bool OperatorManager::isCodomainRational(const Operator * anOperator)
{
	switch( anOperator->getAvmOpCode() )
	{
		case AVM_OPCODE_SIZE:
		{
			return( true );
		}

		default:
		{
			return( isCodomainInteger(anOperator) );
		}
	}
}

bool OperatorManager::isCodomainFloat(const Operator * anOperator)
{
	switch( anOperator->getAvmOpCode() )
	{
		case AVM_OPCODE_SIZE:
		{
			return( true );
		}

		default:
		{
			return( isCodomainRational(anOperator) );
		}
	}
}

bool OperatorManager::isCodomainReal(const Operator * anOperator)
{
	switch( anOperator->getAvmOpCode() )
	{
		case AVM_OPCODE_SIZE:
		{
			return( true );
		}

		default:
		{
			return( isCodomainFloat(anOperator) );
		}
	}
}



/**
 * REGISTRATION
 */
void OperatorManager::registerOp(Operator * anOperator)
{
	if( isalpha( *(anOperator->getNameID().begin()) ) )
	{
		theOperatorsMap[ anOperator->getNameID() ] = anOperator;
	}

	anOperator->setOffset( TABLE_OF_OPERATOR.size() );

	TABLE_OF_OPERATOR.push_back( BF(anOperator) );
}


Operator * OperatorManager::getOp(const std::string & strOperator)
{
	return( theOperatorsMap[ strOperator ] );
}


Operator * OperatorManager::toOperator(
		const std::string & op, Operator * defaultOp)
{
	if( op == "NOT" )  return( OperatorManager::OPERATOR_NOT );
	if( op == "AND" )  return( OperatorManager::OPERATOR_AND );
	if( op == "OR"  )  return( OperatorManager::OPERATOR_OR  );
	if( op == "XOR" )  return( OperatorManager::OPERATOR_XOR );

	if( op == "|;|"  )  return( OperatorManager::OPERATOR_SEQUENCE       );
	if( op == "|;;|" )  return( OperatorManager::OPERATOR_SEQUENCE_WEAK  );
	if( op == "|i|"  )  return( OperatorManager::OPERATOR_INTERLEAVING   );
	if( op == "|~|"  )  return( OperatorManager::OPERATOR_PARTIAL_ORDER );

	return( defaultOp );
}





}
