/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 1 mai 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmcodeSequenceCompiler.h"

#include <fml/expression/AvmCode.h>
#include <fml/expression/StatementConstructor.h>
#include <fml/expression/StatementTypeChecker.h>

#include <fml/operator/Operator.h>
#include <fml/operator/OperatorManager.h>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
// AVMCODE ATOMIC SEQUENCE COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeAtomicSequenceCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( compileStatement(aCTX, aCode) );
}

BF AvmcodeAtomicSequenceCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode optCode( aCode->getOperator() );

	for( const auto & itOperand : aCode.getOperands() )
	{
		optCode->append(
				AVMCODE_COMPILER.decode_optimizeExpression(aCTX, itOperand) );
	}

	return( optCode->hasOneOperand() ? optCode->first().bfCode() : optCode );
}



BFCode AvmcodeAtomicSequenceCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode newCode = AbstractAvmcodeCompiler::compileStatement(aCTX, aCode);

	if( newCode->hasOneOperand() && newCode->first().is< AvmCode >() )
	{
		return( newCode->first().bfCode() );
	}

	return( newCode );
}

BFCode AvmcodeAtomicSequenceCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode optCode( aCode->getOperator() );

	BF optimizedArg;

	for( const auto & itOperand : aCode.getOperands() )
	{
		optimizedArg = AVMCODE_COMPILER.
				decode_optimizeStatement(aCTX, itOperand);

		if( StatementTypeChecker::isComment(optimizedArg) )
		{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
			optCode->append( optimizedArg );
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
		}

		else
		{
			optCode->appendFlat( optimizedArg );
		}
	}

	if( optCode->noOperand() )
	{
		return( StatementConstructor::nopCode() );
	}
	else
	{
		return( optCode->hasOneOperand() ? optCode->first().bfCode() : optCode );
	}
}



////////////////////////////////////////////////////////////////////////////////
// AVMCODE SEQUENCE COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeStrongSequenceCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( compileStatement(aCTX, aCode) );
}

BF AvmcodeStrongSequenceCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( optimizeStatement(aCTX, aCode) );
}



BFCode AvmcodeStrongSequenceCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode newCode = AbstractAvmcodeCompiler::compileStatement(aCTX, aCode);

	if( newCode->hasOneOperand() && newCode->first().is< AvmCode >() )
	{
		return( newCode->first().bfCode() );
	}

	return( newCode );
}

BFCode AvmcodeStrongSequenceCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode optCode( aCode->getOperator() );

	BFCode atomicCode( OperatorManager::OPERATOR_ATOMIC_SEQUENCE );

	BF optimizedArg;

	AvmCode::const_iterator itOperand = aCode->begin();
	AvmCode::const_iterator endOperand = aCode->end();
	for( ; itOperand != endOperand ; ++itOperand )
	{
		optimizedArg = AVMCODE_COMPILER.
				decode_optimizeStatement(aCTX, *itOperand);

		if( StatementTypeChecker::isComment(optimizedArg) )
		{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
			atomicCode->append( optimizedArg );
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
		}

		// ==> StatementTypeChecker::isStrongAtomicSequence(atomicCode)
		else if( StatementTypeChecker::isAtomicStatement(optimizedArg) )
		{
			atomicCode->append( optimizedArg );
		}
		else if( StatementTypeChecker::isStrongAtomicSequence(optimizedArg) )
		{
			atomicCode->append( optimizedArg.to< AvmCode >().getOperands() );
		}
		else if( atomicCode->noOperand() )
		{
			optCode->appendFlat( optimizedArg );
		}
		else if( StatementTypeChecker::isAtomicSequence(optimizedArg) )
		{
			atomicCode->append( optimizedArg.to< AvmCode >().getOperands() );

			optCode->append( atomicCode );

			atomicCode = StatementConstructor::newCode(
					OperatorManager::OPERATOR_ATOMIC_SEQUENCE );
		}
		else if( ((itOperand + 1) != endOperand ) )
		{
			atomicCode->append( optimizedArg );

			optCode->append( atomicCode );

			atomicCode = StatementConstructor::newCode(
					OperatorManager::OPERATOR_ATOMIC_SEQUENCE );
		}
		else // ==> end for(...)
		{
			if( atomicCode->hasOneOperand() )
			{
				optCode->appendFlat( atomicCode->getOperands().pop_last() );
			}
			else if( atomicCode->hasManyOperands() )
			{
				optCode->append( atomicCode );
			}
			atomicCode = BFCode::REF_NULL;

			optCode->appendFlat( optimizedArg );
		}
	}

	if( optCode->hasOperand() )
	{
		if( atomicCode.invalid() )
		{
			//!! NOTHING
		}
		else if( atomicCode->hasOneOperand() )
		{
			optCode->appendFlat( atomicCode->getOperands().pop_last() );
		}
		else if( atomicCode->hasManyOperands() )
		{
			optCode->append( atomicCode );
		}

		else if( optCode->hasOneOperand() )
		{
			return( optCode->first().bfCode() );
		}

		return( optCode );
	}

	else if( atomicCode->noOperand() )
	{
		return( StatementConstructor::nopCode() );
	}
	else
	{
		return( atomicCode->hasOneOperand() ?
				atomicCode->first().bfCode() : atomicCode );
	}
}



BFCode AvmcodeStrongSequenceCompiler::atomizeSequence(const BFCode & aCode)
{
	BFCode optCode( aCode->getOperator() );

	BFCode atomicCode( OperatorManager::OPERATOR_ATOMIC_SEQUENCE );

	BF optimizedArg;

	AvmCode::const_iterator itOperand = aCode->begin();
	AvmCode::const_iterator endOperand = aCode->end();
	for( ; itOperand != endOperand ; ++itOperand )
	{
		optimizedArg = (*itOperand);

		if( StatementTypeChecker::isComment(optimizedArg) )
		{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
			atomicCode->append( optimizedArg );
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
		}

		// ==> StatementTypeChecker::isStrongAtomicSequence(atomicCode)
		else if( StatementTypeChecker::isAtomicStatement(optimizedArg) )
		{
			atomicCode->append( optimizedArg );
		}
		else if( StatementTypeChecker::isStrongAtomicSequence(optimizedArg) )
		{
			atomicCode->append( optimizedArg.to< AvmCode >().getOperands() );
		}
		else if( atomicCode->noOperand() )
		{
			optCode->appendFlat( optimizedArg );
		}
		else if( StatementTypeChecker::isAtomicSequence(optimizedArg) )
		{
			atomicCode->append( optimizedArg.to< AvmCode >().getOperands() );

			optCode->append( atomicCode );

			atomicCode = StatementConstructor::newCode(
					OperatorManager::OPERATOR_ATOMIC_SEQUENCE );
		}
		else if( ((itOperand + 1) != endOperand ) )
		{
			atomicCode->append( optimizedArg );

			optCode->append( atomicCode );

			atomicCode = StatementConstructor::newCode(
					OperatorManager::OPERATOR_ATOMIC_SEQUENCE );
		}
		// ==> end for(...)
		else
		{
			if( atomicCode->hasOneOperand() )
			{
				optCode->appendFlat( atomicCode->getOperands().pop_last() );
			}
			else if( atomicCode->hasManyOperands() )
			{
				optCode->append( atomicCode );
			}
			atomicCode = BFCode::REF_NULL;

			optCode->appendFlat( optimizedArg );
		}
	}


	if( optCode->hasOperand() )
	{
		if( atomicCode.invalid() )
		{
			//!! NOTHING
		}
		else if( atomicCode->hasOneOperand() )
		{
			optCode->appendFlat( atomicCode->getOperands().pop_last() );
		}
		else if( atomicCode->hasManyOperands() )
		{
			optCode->append( atomicCode );
		}

		else if( optCode->hasOneOperand() )
		{
			return( optCode->first().bfCode() );
		}

		return( optCode );
	}
	else if( atomicCode->hasOneOperand() )
	{
		return( atomicCode->first().bfCode() );
	}
	else
	{
		return( atomicCode );
	}
}



////////////////////////////////////////////////////////////////////////////////
// AVMCODE SEQUENCE COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeSequenceCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( compileStatement(aCTX, aCode) );
}

BF AvmcodeSequenceCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode optCode( aCode->getOperator() );

	for( const auto & itOperand : aCode.getOperands() )
	{
		optCode->append(
				AVMCODE_COMPILER.decode_optimizeExpression(aCTX, itOperand) );
	}

	return( optCode->hasOneOperand() ? optCode->first().bfCode() : optCode );
}


BFCode AvmcodeSequenceCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode newCode = AbstractAvmcodeCompiler::compileStatement(aCTX, aCode);

	if( newCode->hasOneOperand() )
	{
		if( newCode->first().is< AvmCode >() )
		{
			return( newCode->first().bfCode() );
		}
	}
	else if( newCode->noOperand() )
	{
		return( StatementConstructor::nopCode() );
	}

	return( newCode );
}


BFCode AvmcodeSequenceCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode optCode( aCode->getOperator() );

	BF optimizedArg;

	for( const auto & itOperand : aCode.getOperands() )
	{
		optimizedArg = AVMCODE_COMPILER.
				decode_optimizeStatement(aCTX, itOperand);

		if( StatementTypeChecker::isComment(optimizedArg) )
		{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
			optCode->append( optimizedArg );
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
		}

		else
		{
			optCode->appendFlat( optimizedArg );
		}
	}

	if( optCode->noOperand() )
	{
		return( StatementConstructor::nopCode() );
	}
	else
	{
		return( optCode->hasOneOperand() ? optCode->first().bfCode() : optCode );
	}
}





}
