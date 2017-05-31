/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 12 avr. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmcodeAssignCompiler.h"

#include <computer/instruction/AvmInstruction.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/ExpressionConstructor.h>
#include <fml/expression/StatementConstructor.h>

#include <fml/operator/OperatorManager.h>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
// AVMCODE ASSIGN COMPILATION
////////////////////////////////////////////////////////////////////////////////

inline BF AvmcodeAssignCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( compileStatement(aCTX, aCode) );
}

inline BF AvmcodeAssignCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	AvmInstruction * argsInstruction = aCode->genInstruction();

	setArgcodeLValue(aCTX, argsInstruction->at(0), aCode->first());

	optimizeArgExpression(aCTX, aCode, 1);
	argsInstruction->at(1).dtype = argsInstruction->at(0).dtype;
	setArgcodeRValue(aCTX, argsInstruction->at(1), aCode->second());

	argsInstruction->computeMainBytecode(
			/*context  */ AVM_ARG_RETURN_CTX,
			/*processor*/ AVM_ARG_MEMORY_RVALUE_CPU,
			/*operation*/ AVM_ARG_SEVAL_RVALUE,
			/*operand  */ AVM_ARG_EXPRESSION_KIND,
			/*dtype    */ argsInstruction->at(0).dtype);

	return( aCode );
}


inline BFCode AvmcodeAssignCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BF lvalue = compileArgLvalue(aCTX, aCode->first());

	if( lvalue.is< InstanceOfData >() )
	{
		aCTX = aCTX->clone(
				lvalue.to_ptr< InstanceOfData >()->getTypeSpecifier() );
	}

	BF rvalue = compileArgRvalue(aCTX, aCode->second());

	BFCode compilCode = StatementConstructor::newCode(
			aCode->getOperator(), lvalue, rvalue );

	return( compilCode );
}

// lvalue =: rvalue;  ==>  [ lvalue , rvalue ]
BFCode AvmcodeAssignCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	AvmInstruction * argsInstruction = aCode->genInstruction();

	setArgcodeLValue(aCTX, argsInstruction->at(0), aCode->first());

	optimizeArgExpression(aCTX, aCode, 1);
	argsInstruction->at(1).dtype = argsInstruction->at(0).dtype;
	setArgcodeRValue(aCTX, argsInstruction->at(1), aCode->second());

	argsInstruction->computeMainBytecode(
			/*context  */ AVM_ARG_STANDARD_CTX,
			/*processor*/ AVM_ARG_STATEMENT_CPU,
			/*operation*/ AVM_ARG_SEVAL_RVALUE,
			/*operand  */ AVM_ARG_STATEMENT_KIND,
			/*dtype    */ argsInstruction->at(0).dtype);

	return( aCode );
}



////////////////////////////////////////////////////////////////////////////////
// AVMCODE ASSIGN AFTER COMPILATION
////////////////////////////////////////////////////////////////////////////////

inline BF AvmcodeAssignAfterCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BF lvalue = compileArgLvalue(aCTX, aCode->first());

	if( lvalue.is< InstanceOfData >() )
	{
		aCTX = aCTX->clone(
				lvalue.to_ptr< InstanceOfData >()->getTypeSpecifier() );
	}

	return( StatementConstructor::newCode( aCode->getOperator(),
			lvalue, lvalue, compileArgRvalue(aCTX, aCode->second()) ) );
}

inline BF AvmcodeAssignAfterCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	AvmInstruction * argsInstruction = aCode->genInstruction();

	setArgcodeLValue(aCTX, argsInstruction->at(0), aCode->first());

	argsInstruction->at(1).dtype = argsInstruction->at(0).dtype;
	setArgcodeRValue(aCTX, argsInstruction->at(1), aCode->second());

	optimizeArgExpression(aCTX, aCode, 2);
	setArgcodeRValue(aCTX, argsInstruction->at(2), aCode->third());

	argsInstruction->computeMainBytecode(
			/*context  */ AVM_ARG_RETURN_CTX,
			/*processor*/ AVM_ARG_MEMORY_RVALUE_CPU,
			/*operation*/ AVM_ARG_SEVAL_RVALUE,
			/*operand  */ AVM_ARG_EXPRESSION_KIND,
			/*dtype    */ argsInstruction->at(0).dtype);

	return( aCode );
}


inline BFCode AvmcodeAssignAfterCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BF lvalue = compileArgLvalue(aCTX, aCode->first());

	if( lvalue.is< InstanceOfData >() )
	{
		aCTX = aCTX->clone(
				lvalue.to_ptr< InstanceOfData >()->getTypeSpecifier() );
	}

	return( StatementConstructor::newCode(OperatorManager::OPERATOR_ASSIGN,
			lvalue, compileArgRvalue(aCTX, aCode->second()) ) );
}

// lvalue =: rvalue;  ==>  [ lvalue , rvalue ]
BFCode AvmcodeAssignAfterCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	AVM_OS_FATAL_ERROR_EXIT
			<< "Unexpected invoke of ASSIGN#AFTER "
				"statement compilation optimizer !!!"
			<< SEND_EXIT;

	return( aCode );
}



////////////////////////////////////////////////////////////////////////////////
// AVMCODE ASSIGN OP COMPILATION
////////////////////////////////////////////////////////////////////////////////

// lvalue op := rvalue;  ==>  [ lvalue , VAL[lvalue] op rvalue ]
inline BF AvmcodeAssignOpCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode expr = aCode->second().bfCode();
	expr = ExpressionConstructor::newCode(expr->getOperator(),
			aCode->first(), expr->first());

	expr = ExpressionConstructor::newCode(
			OperatorManager::OPERATOR_ASSIGN, aCode->first(), expr);

	return( AVMCODE_COMPILER.compileExpression(aCTX, expr) );
}


inline BFCode AvmcodeAssignOpCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode expr = aCode->second().bfCode();
	expr = ExpressionConstructor::newCode(expr->getOperator(),
			aCode->first(), expr->first());

	expr = StatementConstructor::newCode(
			OperatorManager::OPERATOR_ASSIGN, aCode->first(), expr);

	return( AVMCODE_COMPILER.compileStatement(aCTX, expr) );
}



////////////////////////////////////////////////////////////////////////////////
// AVMCODE ASSIGN OP AFTER COMPILATION
////////////////////////////////////////////////////////////////////////////////

// lvalue =: op rvalue;  ==>  [ lvalue , VAL[lvalue] , (VAL[lvalue] op rvalue) ]
inline BF AvmcodeAssignOpAfterCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode expr = aCode->second().bfCode();
	expr = ExpressionConstructor::newCode(expr->getOperator(),
			aCode->first(), expr->first());

	expr = ExpressionConstructor::newCode(
			OperatorManager::OPERATOR_ASSIGN_AFTER, aCode->first(), expr);

	return( AVMCODE_COMPILER.compileExpression(aCTX, expr) );
}


inline BFCode AvmcodeAssignOpAfterCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode expr = aCode->second().bfCode();
	expr = ExpressionConstructor::newCode(expr->getOperator(),
			aCode->first(), expr->first());

	expr = StatementConstructor::newCode(
			OperatorManager::OPERATOR_ASSIGN, aCode->first(), expr);

	return( AVMCODE_COMPILER.compileStatement(aCTX, expr) );
}



////////////////////////////////////////////////////////////////////////////////
// AVMCODE ASSIGN REFERENCE COMPILATION
////////////////////////////////////////////////////////////////////////////////

inline BF AvmcodeAssignRefCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( compileStatement(aCTX, aCode) );
}

inline BF AvmcodeAssignRefCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode optCode = optimizeStatement(aCTX, aCode);

	optCode->getInstruction()->setMainOperand( AVM_ARG_EXPRESSION_KIND );

	return( optCode );
}


inline BFCode AvmcodeAssignRefCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BF lvalue = compileArgLvalue(aCTX, aCode->first());

	if( lvalue.is< InstanceOfData >() )
	{
		aCTX = aCTX->clone(
				lvalue.to_ptr< InstanceOfData >()->getTypeSpecifier() );
	}

	return( StatementConstructor::newCode( aCode->getOperator(),
			lvalue, compileArgLvalue(aCTX, aCode->second()) ) );
}

BFCode AvmcodeAssignRefCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	// lvalue =: lvalue;  <==>  lvalue = $(quote lvalue);
	aCode->setOperator( OperatorManager::OPERATOR_ASSIGN );

	AvmInstruction * argsInstruction = aCode->genInstruction();

	setArgcodeLValueRef(aCTX, argsInstruction->at(0), aCode->first());

	optimizeArgExpression(aCTX, aCode, 1);
	argsInstruction->at(1).dtype = argsInstruction->at(0).dtype;
	setArgcodeLValue(aCTX, argsInstruction->at(1), aCode->second());

	argsInstruction->computeMainBytecode(
			/*context  */ AVM_ARG_STANDARD_CTX,
			/*processor*/ AVM_ARG_STATEMENT_CPU,
			/*operation*/ AVM_ARG_SEVAL_RVALUE,
			/*operand  */ AVM_ARG_STATEMENT_KIND,
			/*dtype    */ argsInstruction->at(0).dtype);

	return( aCode );
}



////////////////////////////////////////////////////////////////////////////////
// AVMCODE ASSIGN Macro COMPILATION
////////////////////////////////////////////////////////////////////////////////

inline BF AvmcodeAssignMacroCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( compileStatement(aCTX, aCode) );
}

inline BF AvmcodeAssignMacroCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode optCode = optimizeStatement(aCTX, aCode);

	optCode->getInstruction()->setMainOperand( AVM_ARG_EXPRESSION_KIND );

	return( optCode );
}


inline BFCode AvmcodeAssignMacroCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BF lvalue = compileArgLvalue(aCTX, aCode->first());

	if( lvalue.is< InstanceOfData >() )
	{
		aCTX = aCTX->clone(
				lvalue.to_ptr< InstanceOfData >()->getTypeSpecifier() );
	}

	return( StatementConstructor::newCode( aCode->getOperator(),
			lvalue, compileArgRvalue(aCTX, aCode->second()) ) );
}

BFCode AvmcodeAssignMacroCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	// lvalue =: lvalue;  <==>  lvalue = $(quote lvalue);
	aCode->setOperator( OperatorManager::OPERATOR_ASSIGN );

	AvmInstruction * argsInstruction = aCode->genInstruction();

	setArgcodeLValueMacro(aCTX, argsInstruction->at(0), aCode->first());

	optimizeArgExpression(aCTX, aCode, 1);
	argsInstruction->at(1).dtype = argsInstruction->at(0).dtype;
	setArgcodeRValue(aCTX, argsInstruction->at(1), aCode->second());
	argsInstruction->at(1).setNopOperation();

	argsInstruction->computeMainBytecode(
			/*context  */ AVM_ARG_STANDARD_CTX,
			/*processor*/ AVM_ARG_STATEMENT_CPU,
			/*operation*/ AVM_ARG_SEVAL_RVALUE,
			/*operand  */ AVM_ARG_STATEMENT_KIND,
			/*dtype    */ argsInstruction->at(0).dtype);

	return( aCode );
}



////////////////////////////////////////////////////////////////////////////////
// AVMCODE ASSIGN UNARY COMPILATION
////////////////////////////////////////////////////////////////////////////////

inline BF AvmcodeAssignUnaryCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( compileStatement(aCTX, aCode) );
}

inline BF AvmcodeAssignUnaryCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	AvmInstruction * argsInstruction = aCode->genInstruction();

	setArgcodeLValue(aCTX, argsInstruction->at(0), aCode->first());

	argsInstruction->computeMainBytecode(
			/*context  */ AVM_ARG_RETURN_CTX,
			/*processor*/ AVM_ARG_MEMORY_RVALUE_CPU,
			/*operation*/ AVM_ARG_SEVAL_RVALUE,
			/*operand  */ AVM_ARG_EXPRESSION_KIND,
			/*dtype    */ argsInstruction->at(0).dtype);

	return( aCode );
}


inline BFCode AvmcodeAssignUnaryCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( StatementConstructor::newCode( aCode->getOperator(),
			compileArgLvalue(aCTX, aCode->first()) ) );
}

BFCode AvmcodeAssignUnaryCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	AvmInstruction * argsInstruction = aCode->genInstruction();

	setArgcodeLValue(aCTX, argsInstruction->at(0), aCode->first());

	argsInstruction->computeMainBytecode(
			/*context  */ AVM_ARG_STANDARD_CTX,
			/*processor*/ AVM_ARG_STATEMENT_CPU,
			/*operation*/ AVM_ARG_SEVAL_RVALUE,
			/*operand  */ AVM_ARG_STATEMENT_KIND,
			/*dtype    */ argsInstruction->at(0).dtype);

	return( aCode );
}



}

