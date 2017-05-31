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

#include "AvmcodeSchedulingCompiler.h"

#include <fml/expression/AvmCode.h>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
// AVMCODE SCHEDULING COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeSchedulingCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( AbstractAvmcodeCompiler::compileStatement(aCTX, aCode) );
}

BF AvmcodeSchedulingCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode optCode( aCode->getOperator() );

	AvmCode::iterator it = aCode->begin();
	AvmCode::iterator endIt = aCode->end();
	for( ; it != endIt ; ++it )
	{
		optCode->append( AVMCODE_COMPILER.decode_optimizeExpression(aCTX, *it) );
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


BFCode AvmcodeSchedulingCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode newCode = AbstractAvmcodeCompiler::compileStatement(aCTX, aCode);

	if( newCode->singleton() && newCode->first().is< AvmCode >() )
	{
		return( newCode->first().bfCode() );
	}

	return( newCode );
}


BFCode AvmcodeSchedulingCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode optCode( aCode->getOperator() );

	AvmCode::iterator it = aCode->begin();
	AvmCode::iterator endIt = aCode->end();
	for( ; it != endIt ; ++it )
	{
		optCode->append( AVMCODE_COMPILER.decode_optimizeStatement(aCTX, *it) );
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
