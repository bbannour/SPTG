/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 22 juin 2010
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef OPERATORLIB_H_
#define OPERATORLIB_H_

#include <util/avm_numeric.h>

#include <string>


namespace sep
{


/**
 * ENUMERATE DECLARATIONS
 */
enum ALGEBRA_QUALIFIER
{
	ALGEBRA_STD,

	ALGEBRA_ASSOC,
	ALGEBRA_LEFT_ASSOC,
	ALGEBRA_RIGHT_ASSOC,

	ALGEBRA_COMM,

	ALGEBRA_ASSOC_COMM
};


enum FIX_NOTATION
{
	NOTATION_INFIX,
	NOTATION_PREFIX,
	NOTATION_SUFFIX,

	NOTATION_FUNCTION,

	NOTATION_STATEMENT
};


enum AVM_OPCODE
{
	AVM_OPCODE_NULL,

	/*
	 ***************************************************************************
	 * AVM NOP STATEMENT
	 ***************************************************************************
	 */
	AVM_OPCODE_NOP,

	AVM_OPCODE_FAILED,
	AVM_OPCODE_THROW,


	/*
	 ***************************************************************************
	 * AVM META STATEMENT
	 ***************************************************************************
	 */
	AVM_OPCODE_INFORMAL,

	AVM_OPCODE_TRACE,

	AVM_OPCODE_DEBUG,

	AVM_OPCODE_COMMENT,

	AVM_OPCODE_QUOTE,

	AVM_OPCODE_META_EVAL,
	AVM_OPCODE_META_RUN,


	/*
	 ***************************************************************************
	 * AVM UFI STATEMENT
	 ***************************************************************************
	 */
	AVM_OPCODE_UFI,

	/*
	 ***************************************************************************
	 * AVM FORM CONSTRUCTOR STATEMENT
	 ***************************************************************************
	 */
	AVM_OPCODE_CTOR,

	/*
	 ***************************************************************************
	 * AVM FORM REGEX STATEMENT
	 ***************************************************************************
	 */
	AVM_OPCODE_REGEX,


	/*
	 ***************************************************************************
	 * AVM MACHINE SELF
	 ***************************************************************************
	 */
	AVM_OPCODE_SELF,
	AVM_OPCODE_SUPER,

	/*
	 ***************************************************************************
	 * AVM MACHINE MANAGING
	 ***************************************************************************
	 */
	AVM_OPCODE_CONTEXT_SWITCHER,

	AVM_OPCODE_PROCESS_STATE_GET,
	AVM_OPCODE_PROCESS_STATE_SET,

	AVM_OPCODE_INIT,
	AVM_OPCODE_FINAL,
	AVM_OPCODE_DESTROY,

	AVM_OPCODE_START,
	AVM_OPCODE_RESTART,
	AVM_OPCODE_STOP,

	AVM_OPCODE_WAIT,

	AVM_OPCODE_SUSPEND,
	AVM_OPCODE_RESUME,

	AVM_OPCODE_IENABLE_INVOKE,
	AVM_OPCODE_ENABLE_INVOKE,
	AVM_OPCODE_ENABLE_SET,

	AVM_OPCODE_IDISABLE_INVOKE,
	AVM_OPCODE_DISABLE_INVOKE,
	AVM_OPCODE_DISABLE_SET,
	AVM_OPCODE_DISABLE_CHILD,
	AVM_OPCODE_DISABLE_SELF,
	AVM_OPCODE_DISABLE_SELVES,

	AVM_OPCODE_IABORT_INVOKE,
	AVM_OPCODE_ABORT_INVOKE,
	AVM_OPCODE_ABORT_SET,
	AVM_OPCODE_ABORT_CHILD,
	AVM_OPCODE_ABORT_SELF,
	AVM_OPCODE_ABORT_SELVES,

	AVM_OPCODE_HISTORY_CLEAR,
	AVM_OPCODE_DEEP_HISTORY_INVOKE,
	AVM_OPCODE_SHALLOW_HISTORY_INVOKE,

	AVM_OPCODE_IRUN,
	AVM_OPCODE_RUN,
	AVM_OPCODE_RTC,

	AVM_OPCODE_SCHEDULE_INVOKE,
	AVM_OPCODE_SCHEDULE_GET,
	AVM_OPCODE_SCHEDULE_IN,
	AVM_OPCODE_SCHEDULE_SET,

	AVM_OPCODE_DEFER_INVOKE,
	AVM_OPCODE_DEFER_GET,
	AVM_OPCODE_DEFER_SET,


	AVM_OPCODE_GOTO,

	AVM_OPCODE_FORK,
	AVM_OPCODE_JOIN,

	AVM_OPCODE_INPUT_ENABLED,

	AVM_OPCODE_RDV,

	AVM_OPCODE_SYNCHRONIZE,


	AVM_OPCODE_INVOKE_NEW,

	AVM_OPCODE_INVOKE_ROUTINE,

	AVM_OPCODE_INVOKE_TRANSITION,

	AVM_OPCODE_INVOKE_METHOD,
	AVM_OPCODE_INVOKE_PROGRAM,
	AVM_OPCODE_INVOKE_FUNCTION,

	AVM_OPCODE_INVOKE_LAMBDA_APPLY,
	AVM_OPCODE_INVOKE_LAMBDA_LET,


	/*
	 ***************************************************************************
	 * AVM MACHINE STATUS
	 ***************************************************************************
	 */
	AVM_OPCODE_STATUS_WAS,
	AVM_OPCODE_STATUS_IS,
	AVM_OPCODE_STATUS_BEING,
	AVM_OPCODE_STATUS_WILL,

	AVM_OPCODE_CHANGED,
	AVM_OPCODE_CHANGED_TO,


	/*
	 ***************************************************************************
	 * AVM PROGRAM SCHEDULING
	 ***************************************************************************
	 */
	AVM_OPCODE_ASYNCHRONOUS,
	AVM_OPCODE_STRONG_SYNCHRONOUS,
	AVM_OPCODE_WEAK_SYNCHRONOUS,

	AVM_OPCODE_INTERLEAVING,
	AVM_OPCODE_PARTIAL_ORDER,


	AVM_OPCODE_PARALLEL,

	// Optimized version of concurrency for RDV synchronization
	AVM_OPCODE_RDV_ASYNCHRONOUS,
	AVM_OPCODE_RDV_STRONG_SYNCHRONOUS,
	AVM_OPCODE_RDV_WEAK_SYNCHRONOUS,

	AVM_OPCODE_RDV_INTERLEAVING,
	AVM_OPCODE_RDV_PARTIAL_ORDER,

	AVM_OPCODE_RDV_PARALLEL,

	AVM_OPCODE_EXCLUSIVE,

	AVM_OPCODE_NONDETERMINISM,

	AVM_OPCODE_PRIOR_GT,
	AVM_OPCODE_PRIOR_LT,

	AVM_OPCODE_SCHEDULE_AND_THEN,
	AVM_OPCODE_SCHEDULE_OR_ELSE,

	AVM_OPCODE_ATOMIC_SEQUENCE,

	AVM_OPCODE_SEQUENCE,
	AVM_OPCODE_SEQUENCE_SIDE,
	AVM_OPCODE_SEQUENCE_WEAK,

	AVM_OPCODE_PRODUCT,


	/*
	 ***************************************************************************
	 * AVM BUFFER MANAGING
	 ***************************************************************************
	 */
	AVM_OPCODE_UPDATE_BUFFER,


	/*
	 ***************************************************************************
	 * LAMBDA STATEMENT
	 ***************************************************************************
	 */
	AVM_OPCODE_APPLY,

	AVM_OPCODE_LAMBDA,


	/*
	 ***************************************************************************
	 * FUNCTIONB STATEMENT
	 ***************************************************************************
	 */
	AVM_OPCODE_FUN,


	/*
	 ***************************************************************************
	 * LET STATEMENT
	 ***************************************************************************
	 */
	AVM_OPCODE_LET,

	/*
	 ***************************************************************************
	 * LOOKUP STATEMENT
	 ***************************************************************************
	 */
	AVM_OPCODE_LOOKUP_INT_EXT,
	AVM_OPCODE_LOOKUP_INT,
	AVM_OPCODE_LOOKUP_NEAREST,
	AVM_OPCODE_LOOKUP_BELOW,
	AVM_OPCODE_LOOKUP_ABOVE,
	AVM_OPCODE_LOOKUP2D_INT_EXT,

	/*
	 ***************************************************************************
	 * AVM PRIMITIVE STATEMENT
	 ***************************************************************************
	 */
	AVM_OPCODE_ASSIGN,
	AVM_OPCODE_ASSIGN_AFTER,
	AVM_OPCODE_ASSIGN_OP,
	AVM_OPCODE_ASSIGN_OP_AFTER,
	AVM_OPCODE_ASSIGN_REF,
	AVM_OPCODE_ASSIGN_MACRO,

	AVM_OPCODE_ASSIGN_NEWFRESH,

	AVM_OPCODE_ASSIGN_RESET,


	AVM_OPCODE_GUARD,
	AVM_OPCODE_TIMED_GUARD,

	AVM_OPCODE_EVENT,

	AVM_OPCODE_CHECK_SAT,

	AVM_OPCODE_INPUT,
	AVM_OPCODE_INPUT_FROM,

	AVM_OPCODE_INPUT_SAVE,

	// Optimized version of INPUT
	AVM_OPCODE_INPUT_ENV,
	AVM_OPCODE_INPUT_VAR,
	AVM_OPCODE_INPUT_FLOW,
	AVM_OPCODE_INPUT_BUFFER,
	AVM_OPCODE_INPUT_RDV,
	AVM_OPCODE_INPUT_MULTI_RDV,
	AVM_OPCODE_INPUT_BROADCAST,
	AVM_OPCODE_INPUT_DELEGATE,

	AVM_OPCODE_OUTPUT,
	AVM_OPCODE_OUTPUT_TO,
	// Optimized version of OUTPUT
	AVM_OPCODE_OUTPUT_ENV,
	AVM_OPCODE_OUTPUT_VAR,
	AVM_OPCODE_OUTPUT_FLOW,
	AVM_OPCODE_OUTPUT_BUFFER,
	AVM_OPCODE_OUTPUT_RDV,
	AVM_OPCODE_OUTPUT_MULTI_RDV,
	AVM_OPCODE_OUTPUT_BROADCAST,
	AVM_OPCODE_OUTPUT_DELEGATE,

	AVM_OPCODE_PRESENT,
	AVM_OPCODE_ABSENT,

	AVM_OPCODE_IF,
	AVM_OPCODE_IFE,

	AVM_OPCODE_WHERE,
	AVM_OPCODE_WHERE_ELSE,

	AVM_OPCODE_FOR,
	AVM_OPCODE_FOREACH,
	AVM_OPCODE_WHILE_DO,
	AVM_OPCODE_DO_WHILE,

	AVM_OPCODE_BREAK,
	AVM_OPCODE_CONTINUE,
	AVM_OPCODE_RETURN,
	AVM_OPCODE_EXIT,

	AVM_OPCODE_STEP_MARK,


	/*
	 ***************************************************************************
	 * AVM QUANTIFIER EXPRESSION
	 ***************************************************************************
	 */
	AVM_OPCODE_EXISTS,
	AVM_OPCODE_FORALL,


	/*
	 ***************************************************************************
	 * AVM PREDICAT EXPRESSION
	 ***************************************************************************
	 */
	AVM_OPCODE_NOT,

	AVM_OPCODE_AND,
	AVM_OPCODE_AND_THEN,

	AVM_OPCODE_NAND,

	AVM_OPCODE_XAND,

	AVM_OPCODE_OR,
	AVM_OPCODE_OR_ELSE,

	AVM_OPCODE_NOR,

	AVM_OPCODE_XOR,
	AVM_OPCODE_XNOR,

	AVM_OPCODE_IMPLIES,


	/*
	 ***************************************************************************
	 * AVM INTEGER BIT A BIT OPERATOR
	 ***************************************************************************
	 */
	AVM_OPCODE_BNOT,

	AVM_OPCODE_BAND,
	AVM_OPCODE_BOR,
	AVM_OPCODE_BXOR,

	AVM_OPCODE_LSHIFT,
	AVM_OPCODE_RSHIFT,


	/*
	 ***************************************************************************
	 * AVM COMPARISON EXPRESSION
	 ***************************************************************************
	 */

	AVM_OPCODE_EQ,
	AVM_OPCODE_NEQ,

	AVM_OPCODE_SEQ,
	AVM_OPCODE_NSEQ,

	AVM_OPCODE_LT,
	AVM_OPCODE_LTE,
	AVM_OPCODE_GT,
	AVM_OPCODE_GTE,


	/*
	 ***************************************************************************
	 * AVM ARITHMETIC EXPRESSION
	 ***************************************************************************
	 */

	AVM_OPCODE_PLUS,
	AVM_OPCODE_MINUS,
	AVM_OPCODE_UMINUS,

	AVM_OPCODE_MULT,
	AVM_OPCODE_POW,

	AVM_OPCODE_DIV,
	AVM_OPCODE_MOD,

	AVM_OPCODE_MIN,
	AVM_OPCODE_MAX,


	/*
	 ***************************************************************************
	 * AVM MATHEMATICAL FUNCTION
	 ***************************************************************************
	 */
	// RANDOM
	AVM_OPCODE_RANDOM,

	// ROUNDING
	AVM_OPCODE_ABS,

	AVM_OPCODE_CEIL,
	AVM_OPCODE_FLOOR,
	AVM_OPCODE_ROUND,
	AVM_OPCODE_TRUNCATE,


	// EXP - LOG
	AVM_OPCODE_SQRT,

	AVM_OPCODE_EXP,
	AVM_OPCODE_LN,
	AVM_OPCODE_LOG,

	// TRIGONOMETRIC
	AVM_OPCODE_SIN,
	AVM_OPCODE_COS,
	AVM_OPCODE_TAN,

	AVM_OPCODE_SINH,
	AVM_OPCODE_COSH,
	AVM_OPCODE_TANH,

	AVM_OPCODE_ASIN,
	AVM_OPCODE_ACOS,
	AVM_OPCODE_ATAN,
	AVM_OPCODE_ATAN2,

	AVM_OPCODE_ASINH,
	AVM_OPCODE_ACOSH,
	AVM_OPCODE_ATANH,


	/*
	 ***************************************************************************
	 * AVM STRING / CONTAINER OPERATOR
	 ***************************************************************************
	 */
	AVM_OPCODE_CONTAINS,

	AVM_OPCODE_IN,
	AVM_OPCODE_NOTIN,

	AVM_OPCODE_SUBSET,
	AVM_OPCODE_SUBSETEQ,

	AVM_OPCODE_INTERSECT,

	AVM_OPCODE_STARTS_WITH,
	AVM_OPCODE_ENDS_WITH,

	AVM_OPCODE_CONCAT,


	AVM_OPCODE_APPEND,

	AVM_OPCODE_REMOVE,
	AVM_OPCODE_CLEAR,

	AVM_OPCODE_RESIZE,

	AVM_OPCODE_SELECT,

	AVM_OPCODE_PUSH,
	AVM_OPCODE_ASSIGN_TOP,
	AVM_OPCODE_TOP,
	AVM_OPCODE_POP,
	AVM_OPCODE_POP_FROM,

	AVM_OPCODE_EMPTY,
	AVM_OPCODE_NONEMPTY,
	AVM_OPCODE_SINGLETON,
	AVM_OPCODE_POPULATED,
	AVM_OPCODE_FULL,

	AVM_OPCODE_SIZE,

	/*
	 ***************************************************************************
	 * CTL* , IOLTL STATEMENT
	 ***************************************************************************
	 */
	AVM_OPCODE_NECESSARILY,  // A :> in All path
	AVM_OPCODE_POSSIBLY,     // E :> the Exist a path

	AVM_OPCODE_GLOBALLY,     // G , \square  , [] :> always in the future
	AVM_OPCODE_EVENTUALLY,   // F , \diamond ' <> :> (or Finally) some time in the Future

	AVM_OPCODE_NEXT,         // X , \circle  , o  :> neXtime

	AVM_OPCODE_UNTIL,        // U :> (p U q ) <=> p holds Until q holds (and ! p)

	AVM_OPCODE_UNLESS,       // W :> (p W q ) <=> Weak Until (or waiting for)
	                         // <=> (G p) or (p U q)
	                         // as long as q is false, p must be true

	AVM_OPCODE_RELEASES,     // R :> (p R q ) <=> q holds Until p holds (with q)
	                         // <=> not ((not p) U (not q))
	AVM_OPCODE_AND_T,
	AVM_OPCODE_OR_T,
	AVM_OPCODE_NOT_T,
	AVM_OPCODE_IMP_T,

	AVM_OPCODE_OBS,

};



enum ENUM_PRINT_OPERATOR_FORMAT
{
	PRINT_OPERATOR_UNDEFINED_FORMAT,

	PRINT_OPERATOR_NAME_FORMAT,

	PRINT_OPERATOR_SYMBOL_FORMAT,

	PRINT_OPERATOR_MIXFIX_FORMAT,

	PRINT_OPERATOR_CAS_QEPCAD_FORMAT
};



class OperatorLib
{

public:

	/**
	 * TEST
	 */
	static bool isPropositional(AVM_OPCODE opcode);


	static std::string to_string(FIX_NOTATION fix);

	static FIX_NOTATION to_fix(const std::string & op,
			FIX_NOTATION defaultFix = NOTATION_INFIX);


	static std::string to_string(AVM_OPCODE opcode,
			ENUM_PRINT_OPERATOR_FORMAT printFormat =
					PRINT_OPERATOR_SYMBOL_FORMAT);

	static AVM_OPCODE toOpcode(const std::string & op,
			AVM_OPCODE defaultOpcode = AVM_OPCODE_NULL);

};


////////////////////////////////////////////////////////////////////////////////
// OperatorFamily
////////////////////////////////////////////////////////////////////////////////

class AvmCode;


class IStatementFamily
{

public:

	typedef std::uint32_t        avm_opcode_family;

	enum
	{
		AVM_STATEMENT_UNDEFINED_FAMILY    = 0x00000,

		AVM_STATEMENT_BASIC_FAMILY        = 0x00001,

		AVM_STATEMENT_GUARD_FAMILY        = 0x00002,


		AVM_STATEMENT_INPUT_FAMILY        = 0x00010,
		AVM_STATEMENT_INPUT_ENV_FAMILY    = 0x00020,
		AVM_STATEMENT_INPUT_SYNC_FAMILY   = 0x00040,
		AVM_STATEMENT_INPUT_ASYNC_FAMILY  = 0x00080,

		AVM_STATEMENT_INPUT_ANY_FAMILY    = AVM_STATEMENT_INPUT_FAMILY
		                                  | AVM_STATEMENT_INPUT_ENV_FAMILY
	                                      | AVM_STATEMENT_INPUT_SYNC_FAMILY
	                                      | AVM_STATEMENT_INPUT_ASYNC_FAMILY,


		AVM_STATEMENT_OUTPUT_FAMILY       = 0x00100,
		AVM_STATEMENT_OUTPUT_ENV_FAMILY   = 0x00200,
		AVM_STATEMENT_OUTPUT_SYNC_FAMILY  = 0x00400,
		AVM_STATEMENT_OUTPUT_ASYNC_FAMILY = 0x00800,

		AVM_STATEMENT_OUTPUT_ANY_FAMILY   = AVM_STATEMENT_OUTPUT_FAMILY
		                                  | AVM_STATEMENT_OUTPUT_ENV_FAMILY
		                                  | AVM_STATEMENT_OUTPUT_SYNC_FAMILY
	                                      | AVM_STATEMENT_OUTPUT_ASYNC_FAMILY,


		AVM_STATEMENT_COM_FAMILY          = AVM_STATEMENT_INPUT_FAMILY
	                                      | AVM_STATEMENT_OUTPUT_FAMILY,

		AVM_STATEMENT_COM_ENV_FAMILY      = AVM_STATEMENT_INPUT_ENV_FAMILY
	                                      | AVM_STATEMENT_OUTPUT_ENV_FAMILY,

		AVM_STATEMENT_COM_ASYNC_FAMILY    = AVM_STATEMENT_INPUT_ASYNC_FAMILY
	                                      | AVM_STATEMENT_OUTPUT_ASYNC_FAMILY,

		AVM_STATEMENT_COM_SYNC_FAMILY     = AVM_STATEMENT_INPUT_SYNC_FAMILY
	                                      | AVM_STATEMENT_OUTPUT_SYNC_FAMILY,

		AVM_STATEMENT_COM_ANY_FAMILY      = AVM_STATEMENT_INPUT_ANY_FAMILY
		                                  | AVM_STATEMENT_OUTPUT_ANY_FAMILY,


		AVM_STATEMENT_UNCONDIONAL_CLASS   = AVM_STATEMENT_BASIC_FAMILY
		                                  | AVM_STATEMENT_COM_ENV_FAMILY,


		AVM_STATEMENT_COM_CONDITIONAL_CLASS = AVM_STATEMENT_COM_FAMILY
		                                  | AVM_STATEMENT_COM_ASYNC_FAMILY
		                                  | AVM_STATEMENT_COM_SYNC_FAMILY,

		AVM_STATEMENT_CONDIONAL_CLASS     = AVM_STATEMENT_GUARD_FAMILY
		                                  | AVM_STATEMENT_COM_CONDITIONAL_CLASS,


		AVM_STATEMENT_MASK_ALL_FAMILY     = 0xFFFFF,

	};


protected:
	/*
	 * ATTRIBUTES
	 */
	avm_opcode_family theStatementFamily;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	IStatementFamily(avm_opcode_family
			aCodeFamily = AVM_STATEMENT_UNDEFINED_FAMILY)
	: theStatementFamily( aCodeFamily )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~IStatementFamily()
	{
		//!! NOTHING
	}

	/**
	 * GETTER - SETTER
	 * theCodeFamily
	 */
	inline avm_opcode_family getStatementFamily() const
	{
		return( theStatementFamily );
	}

	inline bool hasStatementFamily() const
	{
		return( theStatementFamily != AVM_STATEMENT_UNDEFINED_FAMILY );
	}

	inline void addStatementFamily(avm_opcode_family aCodeFamily)
	{
		theStatementFamily |= aCodeFamily;
	}

	inline void setStatementFamily(avm_opcode_family aCodeFamily)
	{
		theStatementFamily = aCodeFamily;
	}


	inline void updateStatementFamily(const AvmCode & aCode)
	{
		theStatementFamily = computeStatementFamily( aCode );
	}

	static avm_opcode_family computeStatementFamily(AVM_OPCODE opcode);

	static avm_opcode_family computeStatementFamily(const AvmCode & aCode);

	/**
	 * TEST
	 * theCodeFamily
	 */
	inline bool hasStatementBasicFamily() const
	{
		return( (theStatementFamily & AVM_STATEMENT_BASIC_FAMILY) != 0 );
	}

	inline bool isStatementBasicFamily() const
	{
		return( theStatementFamily == AVM_STATEMENT_BASIC_FAMILY );
	}


	inline bool hasStatementGuardFamily() const
	{
		return( (theStatementFamily & AVM_STATEMENT_GUARD_FAMILY) != 0 );
	}

	inline bool hasStatementInputFamily() const
	{
		return( (theStatementFamily & AVM_STATEMENT_INPUT_ANY_FAMILY) != 0 );
	}

	inline bool hasStatementOutputFamily() const
	{
		return( (theStatementFamily & AVM_STATEMENT_OUTPUT_ANY_FAMILY) != 0 );
	}

	inline bool hasStatementComFamily() const
	{
		return( (theStatementFamily & AVM_STATEMENT_COM_ANY_FAMILY) != 0 );
	}


	inline bool hasConditionalStatementFamily() const
	{
		return( (theStatementFamily & AVM_STATEMENT_CONDIONAL_CLASS) != 0 );
	}

	inline bool hasConditionalComStatementFamily() const
	{
		return( (theStatementFamily & AVM_STATEMENT_COM_CONDITIONAL_CLASS) != 0 );
	}

	inline bool isGuardConditionalStatementFamily() const
	{
		return( (theStatementFamily & (~ (AVM_STATEMENT_UNCONDIONAL_CLASS |
				AVM_STATEMENT_GUARD_FAMILY)) ) == 0 );
	}


	inline bool hasUnconditionalStatementFamily() const
	{
		return( (theStatementFamily & AVM_STATEMENT_UNCONDIONAL_CLASS) != 0 );
	}

	inline bool isUnconditionalStatementFamily() const
	{
		return( (theStatementFamily & (~ AVM_STATEMENT_UNCONDIONAL_CLASS)) == 0 );
	}


	inline bool hasUnconditionalComStatementFamily() const
	{
		return( (theStatementFamily & AVM_STATEMENT_COM_ENV_FAMILY) != 0 );
	}

	inline bool isUnconditionalComStatementFamily() const
	{
		return( (theStatementFamily & (~ (AVM_STATEMENT_COM_ENV_FAMILY |
				AVM_STATEMENT_BASIC_FAMILY))) == 0 );
	}


	/**
	 * Serialization
	 */
	std::string strStatementFamily(
			avm_opcode_family mask = AVM_STATEMENT_MASK_ALL_FAMILY) const;

};


}

#endif /* OPERATORLIB_H_ */
