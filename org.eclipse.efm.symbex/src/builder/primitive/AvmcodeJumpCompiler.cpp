/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 10 nov. 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmcodeJumpCompiler.h"

#include <fml/expression/AvmCode.h>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
// AVMCODE BREAK EXECUTABLE COMPILATION
////////////////////////////////////////////////////////////////////////////////

BFCode AvmcodeBreakCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( aCode );
}


////////////////////////////////////////////////////////////////////////////////
// AVMCODE CONTINUE EXECUTABLE COMPILATION
////////////////////////////////////////////////////////////////////////////////

BFCode AvmcodeContinueCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( aCode );
}


////////////////////////////////////////////////////////////////////////////////
// AVMCODE EXIT EXECUTABLE COMPILATION
////////////////////////////////////////////////////////////////////////////////

BFCode AvmcodeReturnCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( aCode->noOperand() )
	{
		return( aCode );
	}
	else
	{
		const AvmProgram * aProgram = aCTX->mCompileCtx->getAvmProgram();
		for( ; aProgram != nullptr ; aProgram = aProgram->getAvmProgramContainer() )
		{
			if( aProgram->hasReturn() )
			{
				break;
			}
		}

		if( aProgram != nullptr )
		{
			BFCode retAssignCode( OperatorManager::OPERATOR_ASSIGN,
					aProgram->getReturn(0), compileArgRvalue(
							aCTX->clone(aProgram->getReturnTypeSpecifier(0)),
							aCode->first(), false) );

//			if( aProgram->is< ExecutableForm >() &&
//					( aProgram->to_ptr< ExecutableForm >()->hasKindProcedure() ||
//							aProgram->to_ptr< ExecutableForm >()->hasOnReturn() ) )
//			{
//				return( StatementConstructor::newCode(
//						OperatorManager::OPERATOR_ATOMIC_SEQUENCE, retAssignCode,
//						StatementConstructor::newCode(aCode->getOperator()) ) );
//			}
//			else
			{
				return( StatementConstructor::newCode(
						OperatorManager::OPERATOR_ATOMIC_SEQUENCE, retAssignCode,
						StatementConstructor::newCode(aCode->getOperator()) ) );
			}
		}
		else
		{
			return( StatementConstructor::newCode(aCode->getOperator(),
					compileArgRvalue(aCTX, aCode->first(), false)) );
		}
	}
}

BFCode AvmcodeReturnCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( aCode->hasOperand() )
	{
		AvmInstruction * argsInstruction = aCode->genInstruction();

		optimizeArgExpression(aCTX, aCode, 0);
		argsInstruction->at(0).dtype = TypeManager::UNIVERSAL;
		setArgcodeRValue(aCTX, argsInstruction->at(0), aCode->first());

		argsInstruction->computeMainBytecode(
				/*context  */ AVM_ARG_RETURN_CTX,
				/*processor*/ AVM_ARG_STATEMENT_CPU,
				/*operation*/ AVM_ARG_SEVAL_RVALUE,
				/*operand  */ AVM_ARG_STATEMENT_KIND,
				/*dtype    */ argsInstruction->at(0).dtype);

//		return( optimizeStatementCode(aCTX, aCode) );
	}

	return( aCode );
}


////////////////////////////////////////////////////////////////////////////////
// AVMCODE EXIT EXECUTABLE COMPILATION
////////////////////////////////////////////////////////////////////////////////

BFCode AvmcodeExitCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( aCode->noOperand() )
	{
		return( aCode );
	}
	else
	{
		return( StatementConstructor::newCode(aCode->getOperator(),
				compileArgRvalue(aCTX, aCode->first(), false)) );
	}
}

BFCode AvmcodeExitCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( aCode->hasOperand() )
	{
		AvmInstruction * argsInstruction = aCode->genInstruction();

		optimizeArgExpression(aCTX, aCode, 0);
		argsInstruction->at(0).dtype = TypeManager::UNIVERSAL;
		setArgcodeRValue(aCTX, argsInstruction->at(0), aCode->first());

		argsInstruction->computeMainBytecode(
				/*context  */ AVM_ARG_RETURN_CTX,
				/*processor*/ AVM_ARG_STATEMENT_CPU,
				/*operation*/ AVM_ARG_SEVAL_RVALUE,
				/*operand  */ AVM_ARG_STATEMENT_KIND,
				/*dtype    */ argsInstruction->at(0).dtype);

//		return( optimizeStatementCode(aCTX, aCode) );
	}

	return( aCode );
}


} /* namespace sep */
