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

	for( const auto & itOperand : aCode.getOperands() )
	{
		optCode->append(
				AVMCODE_COMPILER.decode_optimizeExpression(aCTX, itOperand) );
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


BFCode AvmcodeSchedulingCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode newCode = AbstractAvmcodeCompiler::compileStatement(aCTX, aCode);

	if( newCode->hasOneOperand() && newCode->first().is< AvmCode >() )
	{
		return( newCode->first().bfCode() );
	}

	return( newCode );
}


BFCode AvmcodeSchedulingCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode optCode( aCode->getOperator() );

	for( const auto & itOperand : aCode.getOperands() )
	{
		optCode->appendFlat(
				AVMCODE_COMPILER.decode_optimizeStatement(aCTX, itOperand) );
	}

	if( optCode->noOperand() )
	{
		return( StatementConstructor::nopCode() );
	}
	else
	{
		return( optCode->hasOneOperand() ?
				optCode->first().bfCode() : optCode );
	}
}





}
