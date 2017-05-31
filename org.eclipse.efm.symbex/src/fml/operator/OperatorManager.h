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

#ifndef OPERATORMANAGER_H_
#define OPERATORMANAGER_H_

#include <map>

#include <collection/BFContainer.h>

#include <fml/operator/Operator.h>
#include <fml/operator/OperatorLib.h>


namespace sep
{


class OperatorManager
{

public:

	/**
	 * LOADER - DISPOSER
	 */
	static void load();
	static void dispose();


	static Operator * newOperator(
			AVM_OPCODE anAvmOpCode, AVM_OPCODE anOptimizedOpCode,
			const std::string & aFullyQualifiedNameID,
			const std::string & aNameID,
			ALGEBRA_QUALIFIER anAlgebraQualifier,
			FIX_NOTATION aFixQualifier,
			const std::string & aStandardSymbol,
			const std::string & aSyntaxMIXFIX,
			const std::string & aSymbolQEPCAD);


	static inline Operator * newOperatorAssocCom(AVM_OPCODE anAvmOpCode,
			const std::string & aFullyQualifiedNameID,
			const std::string & aNameID,
			const std::string & aStandardSymbol,
			const std::string & aSyntaxMIXFIX,
			const std::string & aSymbolQEPCAD)
	{
		return( newOperator(anAvmOpCode, anAvmOpCode,
				aFullyQualifiedNameID, aNameID,
				ALGEBRA_ASSOC_COMM, NOTATION_INFIX,
				aStandardSymbol, aSyntaxMIXFIX, aSymbolQEPCAD) );
	}

	static inline Operator * newOperatorAssocCom(AVM_OPCODE anAvmOpCode,
			const std::string & aFullyQualifiedNameID,
			const std::string & aNameID,
			const std::string & aStandardSymbol)
	{
		return( newOperator(anAvmOpCode, anAvmOpCode,
				aFullyQualifiedNameID, aNameID,
				ALGEBRA_ASSOC_COMM, NOTATION_INFIX,
				aStandardSymbol, "_" + aStandardSymbol + "_", aStandardSymbol) );
	}

	static inline Operator * newOperatorAssocCom(
			AVM_OPCODE anAvmOpCode, AVM_OPCODE anOptimizedOpCode,
			const std::string & aFullyQualifiedNameID,
			const std::string & aNameID,
			const std::string & aStandardSymbol)
	{
		return( newOperator(anAvmOpCode, anOptimizedOpCode,
				aFullyQualifiedNameID, aNameID,
				ALGEBRA_ASSOC_COMM, NOTATION_INFIX,
				aStandardSymbol, "_" + aStandardSymbol + "_", aStandardSymbol) );
	}


	static inline Operator * newOperatorAssoc(AVM_OPCODE anAvmOpCode,
			const std::string & aFullyQualifiedNameID,
			const std::string & aNameID,
			const std::string & aStandardSymbol)
	{
		return( newOperator(anAvmOpCode, anAvmOpCode,
				aFullyQualifiedNameID, aNameID,
				ALGEBRA_ASSOC, NOTATION_INFIX,
				aStandardSymbol, "_" + aStandardSymbol + "_", aStandardSymbol) );
	}

	static inline Operator * newOperatorLeftAssoc(AVM_OPCODE anAvmOpCode,
			const std::string & aFullyQualifiedNameID,
			const std::string & aNameID,
			const std::string & aStandardSymbol)
	{
		return( newOperator(anAvmOpCode, anAvmOpCode,
				aFullyQualifiedNameID, aNameID,
				ALGEBRA_LEFT_ASSOC, NOTATION_INFIX,
				aStandardSymbol, "_" + aStandardSymbol + "_", aStandardSymbol) );
	}

	static inline Operator * newOperatorRightAssoc(AVM_OPCODE anAvmOpCode,
			const std::string & aFullyQualifiedNameID,
			const std::string & aNameID,
			const std::string & aStandardSymbol)
	{
		return( newOperator(anAvmOpCode, anAvmOpCode,
				aFullyQualifiedNameID, aNameID,
				ALGEBRA_RIGHT_ASSOC, NOTATION_INFIX,
				aStandardSymbol, "_" + aStandardSymbol + "_", aStandardSymbol) );
	}


	static inline Operator * newOperatorStdInfix(AVM_OPCODE anAvmOpCode,
			const std::string & aFullyQualifiedNameID,
			const std::string & aNameID,
			const std::string & aStandardSymbol,
			const std::string & aSyntaxMIXFIX,
			const std::string & aSymbolQEPCAD)
	{
		return( newOperator(anAvmOpCode, anAvmOpCode,
				aFullyQualifiedNameID, aNameID,
				ALGEBRA_STD, NOTATION_INFIX,
				aStandardSymbol, aSyntaxMIXFIX, aSymbolQEPCAD) );
	}

	static inline Operator * newOperatorStdInfix(AVM_OPCODE anAvmOpCode,
			const std::string & aFullyQualifiedNameID,
			const std::string & aNameID,
			const std::string & aStandardSymbol)
	{
		return( newOperator(anAvmOpCode, anAvmOpCode,
				aFullyQualifiedNameID, aNameID,
				ALGEBRA_STD, NOTATION_INFIX,
				aStandardSymbol, "_" + aStandardSymbol + "_", aStandardSymbol) );
	}


	static inline Operator * newOperatorStdPrefix(AVM_OPCODE anAvmOpCode,
			const std::string & aFullyQualifiedNameID,
			const std::string & aNameID,
			const std::string & aStandardSymbol,
			const std::string & aSyntaxMIXFIX,
			const std::string & aSymbolQEPCAD)
	{
		return( newOperator(anAvmOpCode, anAvmOpCode,
				aFullyQualifiedNameID, aNameID,
				ALGEBRA_STD, NOTATION_PREFIX,
				aStandardSymbol, aSyntaxMIXFIX, aSymbolQEPCAD) );
	}

	static inline Operator * newOperatorStdPrefix(AVM_OPCODE anAvmOpCode,
			const std::string & aFullyQualifiedNameID,
			const std::string & aNameID, const std::string & aStandardSymbol)
	{
		return( newOperator(anAvmOpCode, anAvmOpCode,
				aFullyQualifiedNameID, aNameID,
				ALGEBRA_STD, NOTATION_PREFIX,
				aStandardSymbol, aStandardSymbol + "_", aStandardSymbol) );
	}


	static inline Operator * newOpStatement(
			AVM_OPCODE anAvmOpCode, AVM_OPCODE anOptimizedOpCode,
			const std::string & aFullyQualifiedNameID,
			const std::string & aNameID)
	{
		return( newOperator(anAvmOpCode, anOptimizedOpCode,
				aFullyQualifiedNameID, aNameID,
				ALGEBRA_STD, NOTATION_STATEMENT,
				aNameID, aNameID, aNameID) );
	}


	/**
	 * TESTER
	 */
	static bool isQuote(const Operator * anOperator);

	static bool isMeta(const Operator * anOperator);
	static bool isMetaEval(const Operator * anOperator);
	static bool isMetaRun(const Operator * anOperator);


	static inline bool isAssign(const Operator * anOperator)
	{
		return( isAssignBinary(anOperator) || isAssignUnary(anOperator) );
	}

	static bool isAssignBinary(const Operator * anOperator);
	static bool isAssignUnary(const Operator * anOperator);


	static bool isUfi(const Operator * anOperator);
	static bool isCtor(const Operator * anOperator);

	static bool isUfiOrCtor(const Operator * anOperator);

	static bool isNewfresh(const Operator * anOperator);

	static bool isSequence(const Operator * anOperator);

	static bool isSchedule(const Operator * anOperator);

	static bool isMachine(const Operator * anOperator);

	static bool isActivity(const Operator * anOperator);

	static bool isCommunication(const Operator * anOperator);

	static bool isConditionnal(const Operator * anOperator);

	static bool isStatement(const Operator * anOperator);

	static bool isAtomicStatement(const Operator * anOperator);


	static bool isArithmetic(const Operator * anOperator);

	static bool isBoolean(const Operator * anOperator);
	static bool isRelational(const Operator * anOperator);
	static bool isPropositional(const Operator * anOperator);

	static bool isTemporalLogic(const Operator * anOperator);


	static bool isCharacter(const Operator * anOperator);
	static bool isString(const Operator * anOperator);

	static bool isLookup(const Operator * anOperator);
	static bool isLookup1D(const Operator * anOperator);
	static bool isLookup2D(const Operator * anOperator);

	static bool isContainerElementAccess(const Operator * anOperator);

	static bool isContainerOperation(const Operator * anOperator);


	/**
	 * Codomain of function
	 */
	static bool isCodomainBoolean(const Operator * anOperator);

	static bool isCodomainCharacter(const Operator * anOperator);

	static bool isCodomainString(const Operator * anOperator);

	static bool isCodomainInteger(const Operator * anOperator);

	static bool isCodomainRational(const Operator * anOperator);

	static bool isCodomainFloat(const Operator * anOperator);

	static bool isCodomainReal(const Operator * anOperator);



	/**
	 * REGISTRATION
	 */
	static void registerOp(Operator * anOperator);
	static Operator * getOp(const std::string & strOperator);

	static Operator * toOperator(const std::string & op, Operator * defaultOp);

	/**
	 * ATTRIBUTES
	 */
	static std::map< std::string , Operator * > theOperatorsMap;

	static BFVector TABLE_OF_OPERATOR;


#define CONST_BF_OP(op)   \
	sep::OperatorManager::TABLE_OF_OPERATOR[ op->getOffset() ]

#define CONST_BF_OPERATOR(op)   \
	sep::OperatorManager::TABLE_OF_OPERATOR[   \
		sep::OperatorManager::OPERATOR_##op->getOffset() ]




	/*
	 ***************************************************************************
	 * AVM NOP STATEMENT
	 ***************************************************************************
	 */
	static Operator * OPERATOR_NOP;


	/*
	 ***************************************************************************
	 * AVM META STATEMENT
	 ***************************************************************************
	 */
	static Operator * OPERATOR_INFORMAL;

	static Operator * OPERATOR_TRACE;

	static Operator * OPERATOR_DEBUG;

	static Operator * OPERATOR_COMMENT;

	static Operator * OPERATOR_QUOTE;

	static Operator * OPERATOR_META_EVAL;
	static Operator * OPERATOR_META_RUN;

	/*
	 ***************************************************************************
	 * AVM UFI STATEMENT
	 ***************************************************************************
	 */
	static Operator * OPERATOR_UFI;


	/*
	 ***************************************************************************
	 * AVM FORM CONSTRUCTOR STATEMENT
	 ***************************************************************************
	 */
	static Operator * OPERATOR_CTOR;


	/*
	 ***************************************************************************
	 * AVM MACHINE MANAGING
	 ***************************************************************************
	 */
	static Operator * OPERATOR_CONTEXT_SWITCHER;

	static Operator * OPERATOR_INIT;
	static Operator * OPERATOR_FINAL;
	static Operator * OPERATOR_DESTROY;

	static Operator * OPERATOR_START;
	static Operator * OPERATOR_RESTART;
	static Operator * OPERATOR_STOP;

	static Operator * OPERATOR_WAIT;

	static Operator * OPERATOR_SUSPEND;
	static Operator * OPERATOR_RESUME;


	static Operator * OPERATOR_IENABLE_INVOKE;
	static Operator * OPERATOR_ENABLE_INVOKE;
	static Operator * OPERATOR_ENABLE_SET;

	static Operator * OPERATOR_IDISABLE_INVOKE;
	static Operator * OPERATOR_DISABLE_INVOKE;
	static Operator * OPERATOR_DISABLE_SET;
	static Operator * OPERATOR_DISABLE_CHILD;
	static Operator * OPERATOR_DISABLE_SELF;
	static Operator * OPERATOR_DISABLE_SELVES;

	static Operator * OPERATOR_IABORT_INVOKE;
	static Operator * OPERATOR_ABORT_INVOKE;
	static Operator * OPERATOR_ABORT_SET;
	static Operator * OPERATOR_ABORT_CHILD;
	static Operator * OPERATOR_ABORT_SELF;
	static Operator * OPERATOR_ABORT_SELVES;

	static Operator * OPERATOR_HISTORY_CLEAR;
	static Operator * OPERATOR_DEEP_HISTORY_INVOKE;
	static Operator * OPERATOR_SHALLOW_HISTORY_INVOKE;

	static Operator * OPERATOR_IRUN;
	static Operator * OPERATOR_RUN;
	static Operator * OPERATOR_RTC;

	static Operator * OPERATOR_INVOKE_NEW;

	static Operator * OPERATOR_INVOKE_ROUTINE;

	static Operator * OPERATOR_INVOKE_TRANSITION;

	static Operator * OPERATOR_INVOKE_METHOD;
	static Operator * OPERATOR_INVOKE_PROGRAM;
	static Operator * OPERATOR_INVOKE_FUNCTION;

	static Operator * OPERATOR_INVOKE_LAMBDA_APPLY;
	static Operator * OPERATOR_INVOKE_LAMBDA_LET;

	static Operator * OPERATOR_GOTO;

	static Operator * OPERATOR_SCHEDULE_INVOKE;
	static Operator * OPERATOR_SCHEDULE_GET;
	static Operator * OPERATOR_SCHEDULE_IN;
	static Operator * OPERATOR_SCHEDULE_SET;

	static Operator * OPERATOR_DEFER_INVOKE;
	static Operator * OPERATOR_DEFER_GET;
	static Operator * OPERATOR_DEFER_SET;

	static Operator * OPERATOR_FORK;
	static Operator * OPERATOR_JOIN;

	static Operator * OPERATOR_INPUT_ENABLED;

	static Operator * OPERATOR_RDV;

	static Operator * OPERATOR_SYNCHRONIZE;


	/*
	 ***************************************************************************
	 * AVM DATA STATUS
	 ***************************************************************************
	 */
	static Operator * OPERATOR_STATUS_WAS;
	static Operator * OPERATOR_STATUS_IS;
	static Operator * OPERATOR_STATUS_BEING;
	static Operator * OPERATOR_STATUS_WILL;

	static Operator * OPERATOR_CHANGED;
	static Operator * OPERATOR_CHANGED_TO;


	/*
	 ***************************************************************************
	 * AVM PROGRAM SCHEDULING
	 ***************************************************************************
	 */
	static Operator * OPERATOR_ASYNCHRONOUS;
	static Operator * OPERATOR_STRONG_SYNCHRONOUS;
	static Operator * OPERATOR_WEAK_SYNCHRONOUS;

	static Operator * OPERATOR_INTERLEAVING;
	static Operator * OPERATOR_PARTIAL_ORDER_REDUCTION;

	static Operator * OPERATOR_PARALLEL;

	static Operator * OPERATOR_RDV_ASYNCHRONOUS;
	static Operator * OPERATOR_RDV_STRONG_SYNCHRONOUS;
	static Operator * OPERATOR_RDV_WEAK_SYNCHRONOUS;

	static Operator * OPERATOR_RDV_INTERLEAVING;
	static Operator * OPERATOR_RDV_PARTIAL_ORDER_REDUCTION;

	static Operator * OPERATOR_RDV_PARALLEL;

	static Operator * OPERATOR_EXCLUSIVE;
	static Operator * OPERATOR_NONDETERMINISM;

	static Operator * OPERATOR_PRIOR_GT;
	static Operator * OPERATOR_PRIOR_LT;

	static Operator * OPERATOR_SCHEDULE_AND_THEN;
	static Operator * OPERATOR_SCHEDULE_OR_ELSE;

	static Operator * OPERATOR_ATOMIC_SEQUENCE;

	static Operator * OPERATOR_SEQUENCE;
	static Operator * OPERATOR_SEQUENCE_SIDE;
	static Operator * OPERATOR_SEQUENCE_WEAK;

	static Operator * OPERATOR_PRODUCT;


	/*
	 ***************************************************************************
	 * AVM BUFFER MANAGING
	 ***************************************************************************
	 */
	static Operator * OPERATOR_UPDATE_BUFFER;


	/*
	 ***************************************************************************
	 * LAMBDA STATEMENT
	 ***************************************************************************
	 */
	static Operator * OPERATOR_APPLY;

	static Operator * OPERATOR_LAMBDA;


	/*
	 ***************************************************************************
	 * LET STATEMENT
	 ***************************************************************************
	 */
	static Operator * OPERATOR_LET;


	/*
	 ***************************************************************************
	 * AVM PRIMITIVE STATEMENT
	 ***************************************************************************
	 */
	static Operator * OPERATOR_ASSIGN;
	static Operator * OPERATOR_ASSIGN_AFTER;
	static Operator * OPERATOR_ASSIGN_OP;
	static Operator * OPERATOR_ASSIGN_OP_AFTER;
	static Operator * OPERATOR_ASSIGN_REF;
	static Operator * OPERATOR_ASSIGN_MACRO;

	static Operator * OPERATOR_ASSIGN_NEWFRESH;

	static Operator * OPERATOR_ASSIGN_RESET;

	static Operator * OPERATOR_GUARD;
	static Operator * OPERATOR_TIMED_GUARD;

	static Operator * OPERATOR_EVENT;
	static Operator * OPERATOR_CHECK_SAT;


	static Operator * OPERATOR_INPUT;
	static Operator * OPERATOR_INPUT_FROM;

	static Operator * OPERATOR_INPUT_SAVE;

	// Optimized version of INPUT
	static Operator * OPERATOR_INPUT_VAR;
	static Operator * OPERATOR_INPUT_FLOW;

	static Operator * OPERATOR_INPUT_ENV;
	static Operator * OPERATOR_INPUT_BUFFER;
	static Operator * OPERATOR_INPUT_RDV;
	static Operator * OPERATOR_INPUT_BROADCAST;
	static Operator * OPERATOR_INPUT_DELEGATE;


	static Operator * OPERATOR_OUTPUT;
	static Operator * OPERATOR_OUTPUT_TO;

	// Optimized version of OUTPUT
	static Operator * OPERATOR_OUTPUT_VAR;
	static Operator * OPERATOR_OUTPUT_FLOW;

	static Operator * OPERATOR_OUTPUT_ENV;
	static Operator * OPERATOR_OUTPUT_BUFFER;
	static Operator * OPERATOR_OUTPUT_RDV;
	static Operator * OPERATOR_OUTPUT_BROADCAST;
	static Operator * OPERATOR_OUTPUT_DELEGATE;


	static Operator * OPERATOR_PRESENT;
	static Operator * OPERATOR_ABSENT;


	static Operator * OPERATOR_IF;
	static Operator * OPERATOR_IFE;

	static Operator * OPERATOR_FOR;
	static Operator * OPERATOR_FOREACH;
	static Operator * OPERATOR_WHILE_DO;
	static Operator * OPERATOR_DO_WHILE;

	static Operator * OPERATOR_BREAK;
	static Operator * OPERATOR_CONTINUE;
	static Operator * OPERATOR_RETURN;
	static Operator * OPERATOR_EXIT;

	static Operator * OPERATOR_STEP_MARK;


	/*
	 ***************************************************************************
	 * AVM PREDICAT EXPRESSION
	 ***************************************************************************
	 */
	static Operator * OPERATOR_EXIST;
	static Operator * OPERATOR_FORALL;

	static Operator * OPERATOR_NOT;

	static Operator * OPERATOR_AND;
	static Operator * OPERATOR_AND_THEN;

	static Operator * OPERATOR_NAND;

	static Operator * OPERATOR_XAND;

	static Operator * OPERATOR_OR;
	static Operator * OPERATOR_OR_ELSE;

	static Operator * OPERATOR_NOR;

	static Operator * OPERATOR_XOR;
	static Operator * OPERATOR_XNOR;


	/*
	 ***************************************************************************
	 * AVM BITWISE EXPRESSION
	 ***************************************************************************
	 */
	static Operator * OPERATOR_BNOT;

	static Operator * OPERATOR_BAND;
	static Operator * OPERATOR_BOR;
	static Operator * OPERATOR_BXOR;

	static Operator * OPERATOR_LSHIFT;
	static Operator * OPERATOR_RSHIFT;


	/*
	 ***************************************************************************
	 * AVM SYNTAXIC COMPARISON EXPRESSION
	 ***************************************************************************
	 */
	static Operator * OPERATOR_SEQ;
	static Operator * OPERATOR_NSEQ;


	/*
	 ***************************************************************************
	 * AVM COMPARISON EXPRESSION
	 ***************************************************************************
	 */
	static Operator * OPERATOR_EQ;
	static Operator * OPERATOR_NEQ;

	static Operator * OPERATOR_LT;
	static Operator * OPERATOR_LTE;
	static Operator * OPERATOR_GT;
	static Operator * OPERATOR_GTE;


	/*
	 ***************************************************************************
	 * AVM ARITHMETIC EXPRESSION
	 ***************************************************************************
	 */
	static Operator * OPERATOR_PLUS;
	static Operator * OPERATOR_MINUS;
	static Operator * OPERATOR_UMINUS;

	static Operator * OPERATOR_MULT;
	static Operator * OPERATOR_POW;

	static Operator * OPERATOR_DIV;
	static Operator * OPERATOR_MOD;

	static Operator * OPERATOR_MIN;
	static Operator * OPERATOR_MAX;


	/*
	 ***************************************************************************
	 * LOOKUP STATEMENT
	 ***************************************************************************
	 */
	static Operator * OPERATOR_LOOKUP_INT_EXT;
	static Operator * OPERATOR_LOOKUP_INT;
	static Operator * OPERATOR_LOOKUP_NEAREST;
	static Operator * OPERATOR_LOOKUP_BELOW;
	static Operator * OPERATOR_LOOKUP_ABOVE;
	static Operator * OPERATOR_LOOKUP2D_INT_EXT;


	/*
	 ***************************************************************************
	 * AVM MATHEMATICAL FUNCTION
	 ***************************************************************************
	 */
	// ROUNDING
	static Operator * OPERATOR_RANDOM;

	static Operator * OPERATOR_ABS;

	static Operator * OPERATOR_CEIL;
	static Operator * OPERATOR_FLOOR;
	static Operator * OPERATOR_ROUND;
	static Operator * OPERATOR_TRUNCATE;

	// EXP - LOG
	static Operator * OPERATOR_SQRT;

	static Operator * OPERATOR_EXP;
	static Operator * OPERATOR_LN;
	static Operator * OPERATOR_LOG;

	// TRIGONOMETRIC
	static Operator * OPERATOR_SIN;
	static Operator * OPERATOR_COS;
	static Operator * OPERATOR_TAN;

	static Operator * OPERATOR_SINH;
	static Operator * OPERATOR_COSH;
	static Operator * OPERATOR_TANH;

	static Operator * OPERATOR_ASIN;
	static Operator * OPERATOR_ACOS;
	static Operator * OPERATOR_ATAN;
	static Operator * OPERATOR_ATAN2;

	static Operator * OPERATOR_ASINH;
	static Operator * OPERATOR_ACOSH;
	static Operator * OPERATOR_ATANH;

	/*
	 ***************************************************************************
	 * AVM STRING / COLLECTION OPERATOR
	 ***************************************************************************
	 */
	static Operator * OPERATOR_CONTAINS;

	static Operator * OPERATOR_IN;
	static Operator * OPERATOR_NOTIN;

	static Operator * OPERATOR_SUBSET;
	static Operator * OPERATOR_SUBSETEQ;

	static Operator * OPERATOR_INTERSECT;

	static Operator * OPERATOR_STARTS_WITH;
	static Operator * OPERATOR_ENDS_WITH;

	static Operator * OPERATOR_CONCAT;

	static Operator * OPERATOR_APPEND;

	static Operator * OPERATOR_REMOVE;
	static Operator * OPERATOR_CLEAR;

	static Operator * OPERATOR_RESIZE;

	static Operator * OPERATOR_SELECT;

	static Operator * OPERATOR_PUSH;
	static Operator * OPERATOR_ASSIGN_TOP;
	static Operator * OPERATOR_TOP;
	static Operator * OPERATOR_POP;
	static Operator * OPERATOR_POP_FROM;

	static Operator * OPERATOR_EMPTY;
	static Operator * OPERATOR_NONEMPTY;
	static Operator * OPERATOR_SINGLETON;
	static Operator * OPERATOR_POPULATED;
	static Operator * OPERATOR_FULL;

	static Operator * OPERATOR_SIZE;


	/*
	 ***************************************************************************
	 * IOLTL BEHAVIORAL PREDICAT
	 ***************************************************************************
	 */
	static Operator * OPERATOR_GLOBALLY;
	static Operator * OPERATOR_UNTIL;
	static Operator * OPERATOR_NEXT;
	static Operator * OPERATOR_EVENTUALLY;
	static Operator * OPERATOR_RELEASES;
	static Operator * OPERATOR_OBS;


	/*
	 ***************************************************************************
	 * IOLTL LOGICAL PREDICAT
	 ***************************************************************************
	 */
	static Operator * OPERATOR_AND_T;
	static Operator * OPERATOR_OR_T;
	static Operator * OPERATOR_NOT_T;
	static Operator * OPERATOR_IMP_T;




};

}

#endif /* OPERATORMANAGER_H_ */
