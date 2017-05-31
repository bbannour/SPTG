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

	AvmCode::iterator it = aCode->begin();
	AvmCode::iterator endIt = aCode->end();
	for( ; it != endIt ; ++it )
	{
		optCode->append(
				AVMCODE_COMPILER.decode_optimizeExpression(aCTX, *it) );
	}

	return( optCode->singleton() ? optCode->first().bfCode() : optCode );
}



BFCode AvmcodeAtomicSequenceCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode newCode = AbstractAvmcodeCompiler::compileStatement(aCTX, aCode);

	if( newCode->singleton() && newCode->first().is< AvmCode >() )
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

	AvmCode::iterator it = aCode->begin();
	AvmCode::iterator endIt = aCode->end();
	for( ; it != endIt ; ++it )
	{
		optimizedArg = AVMCODE_COMPILER.decode_optimizeStatement(aCTX, *it);

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

	if( optCode->empty() )
	{
		return( StatementConstructor::nopCode() );
	}
	else
	{
		return( optCode->singleton() ? optCode->first().bfCode() : optCode );
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

	if( newCode->singleton() && newCode->first().is< AvmCode >() )
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

	AvmCode::iterator it = aCode->begin();
	AvmCode::iterator endIt = aCode->end();
	for( ; it != endIt ; ++it )
	{
		optimizedArg = AVMCODE_COMPILER.decode_optimizeStatement(aCTX, *it);

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
			atomicCode->append( optimizedArg.to_ptr< AvmCode >()->getArgs() );
		}
		else if( atomicCode->empty() )
		{
			optCode->appendFlat( optimizedArg );
		}
		else if( StatementTypeChecker::isAtomicSequence(optimizedArg) )
		{
			atomicCode->append( optimizedArg.to_ptr< AvmCode >()->getArgs() );

			optCode->append( atomicCode );

			atomicCode = StatementConstructor::newCode(
					OperatorManager::OPERATOR_ATOMIC_SEQUENCE );
		}
		else if( ((it + 1) != endIt ) )
		{
			atomicCode->append( optimizedArg );

			optCode->append( atomicCode );

			atomicCode = StatementConstructor::newCode(
					OperatorManager::OPERATOR_ATOMIC_SEQUENCE );
		}
		else // ==> end for(...)
		{
			if( atomicCode->singleton() )
			{
				optCode->appendFlat( atomicCode->pop_last() );
			}
			else if( atomicCode->populated() )
			{
				optCode->append( atomicCode );
			}
			atomicCode = BFCode::REF_NULL;

			optCode->appendFlat( optimizedArg );
		}
	}

	if( optCode->nonempty() )
	{
		if( atomicCode.invalid() )
		{
			//!! NOTHING
		}
		else if( atomicCode->singleton() )
		{
			optCode->appendFlat( atomicCode->pop_last() );
		}
		else if( atomicCode->populated() )
		{
			optCode->append( atomicCode );
		}

		else if( optCode->singleton() )
		{
			return( optCode->first().bfCode() );
		}

		return( optCode );
	}

	else if( atomicCode->empty() )
	{
		return( StatementConstructor::nopCode() );
	}
	else
	{
		return( atomicCode->singleton() ?
				atomicCode->first().bfCode() : atomicCode );
	}
}



BFCode AvmcodeStrongSequenceCompiler::atomizeSequence(const BFCode & aCode)
{
	BFCode optCode( aCode->getOperator() );

	BFCode atomicCode( OperatorManager::OPERATOR_ATOMIC_SEQUENCE );

	BF optimizedArg;

	AvmCode::iterator it = aCode->begin();
	AvmCode::iterator endIt = aCode->end();
	for( ; it != endIt ; ++it )
	{
		optimizedArg = (*it);

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
			atomicCode->append( optimizedArg.to_ptr< AvmCode >()->getArgs() );
		}
		else if( atomicCode->empty() )
		{
			optCode->appendFlat( optimizedArg );
		}
		else if( StatementTypeChecker::isAtomicSequence(optimizedArg) )
		{
			atomicCode->append( optimizedArg.to_ptr< AvmCode >()->getArgs() );

			optCode->append( atomicCode );

			atomicCode = StatementConstructor::newCode(
					OperatorManager::OPERATOR_ATOMIC_SEQUENCE );
		}
		else if( ((it + 1) != endIt ) )
		{
			atomicCode->append( optimizedArg );

			optCode->append( atomicCode );

			atomicCode = StatementConstructor::newCode(
					OperatorManager::OPERATOR_ATOMIC_SEQUENCE );
		}
		// ==> end for(...)
		else
		{
			if( atomicCode->singleton() )
			{
				optCode->appendFlat( atomicCode->pop_last() );
			}
			else if( atomicCode->populated() )
			{
				optCode->append( atomicCode );
			}
			atomicCode = BFCode::REF_NULL;

			optCode->appendFlat( optimizedArg );
		}
	}


	if( optCode->nonempty() )
	{
		if( atomicCode.invalid() )
		{
			//!! NOTHING
		}
		else if( atomicCode->singleton() )
		{
			optCode->appendFlat( atomicCode->pop_last() );
		}
		else if( atomicCode->populated() )
		{
			optCode->append( atomicCode );
		}

		else if( optCode->singleton() )
		{
			return( optCode->first().bfCode() );
		}

		return( optCode );
	}
	else if( atomicCode->singleton() )
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

	AvmCode::iterator it = aCode->begin();
	AvmCode::iterator endIt = aCode->end();
	for( ; it != endIt ; ++it )
	{
		optCode->append(
				AVMCODE_COMPILER.decode_optimizeExpression(aCTX, *it) );
	}

	return( optCode->singleton() ? optCode->first().bfCode() : optCode );
}


BFCode AvmcodeSequenceCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode newCode = AbstractAvmcodeCompiler::compileStatement(aCTX, aCode);

	if( newCode->singleton() )
	{
		if( newCode->first().is< AvmCode >() )
		{
			return( newCode->first().bfCode() );
		}
	}
	else if( newCode->empty() )
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

	AvmCode::iterator it = aCode->begin();
	AvmCode::iterator endIt = aCode->end();
	for( ; it != endIt ; ++it )
	{
		optimizedArg = AVMCODE_COMPILER.decode_optimizeStatement(aCTX, *it);

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

	if( optCode->empty() )
	{
		return( StatementConstructor::nopCode() );
	}
	else
	{
		return( optCode->singleton() ? optCode->first().bfCode() : optCode );
	}
}





}
