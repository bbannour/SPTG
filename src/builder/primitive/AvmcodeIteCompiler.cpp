/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 26 nov. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmcodeIteCompiler.h"

#include <builder/primitive/AvmcodeCompiler.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/StatementConstructor.h>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
// AVMCODE IF THE ELSE COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeIteCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode aCompiledCode( aCode->getOperator(),
			compileArgRvalue(aCTX, TypeManager::BOOLEAN, aCode->first()),
			compileArgRvalue(aCTX, aCode->second()) );

	if( aCode->isOpCode( AVM_OPCODE_IFE ) )
	{
		aCompiledCode->append( compileArgRvalue(aCTX, aCode->operand(2)) );
	}

	return( aCompiledCode );
}

BF AvmcodeIteCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode optimizedCode( aCode->getOperator(),
			AVMCODE_COMPILER.decode_optimizeExpression(aCTX, aCode->first()),
			AVMCODE_COMPILER.decode_optimizeExpression(aCTX, aCode->second()) );

	AvmInstruction * argsInstruction =
			optimizedCode->newInstruction( aCode->size() );

	argsInstruction->at(0).dtype = TypeManager::BOOLEAN;
	setArgcodeRValue(aCTX, argsInstruction->at(0), optimizedCode->first());

	argsInstruction->at(1).dtype = TypeManager::UNIVERSAL;
	setArgcodeRValue(aCTX, argsInstruction->at(1), optimizedCode->second());

	if( aCode->isOpCode( AVM_OPCODE_IFE ) )
	{
		optimizedCode->append( AVMCODE_COMPILER.decode_optimizeExpression(
				aCTX, aCode->operand(2)) );

		argsInstruction->at(2).dtype = TypeManager::UNIVERSAL;
		setArgcodeRValue(aCTX,
				argsInstruction->at(2), optimizedCode->operand(2));
	}

	argsInstruction->computeMainBytecode(
			/*context  */ AVM_ARG_STANDARD_CTX,
			/*processor*/ AVM_ARG_ARITHMETIC_LOGIC_CPU,
			/*operation*/ AVM_ARG_SEVAL_RVALUE,
			/*operand  */ AVM_ARG_EXPRESSION_KIND);

	return( optimizedCode );
}



BFCode AvmcodeIteCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode aCompiledCode( aCode->getOperator(),
			compileArgRvalue(aCTX, TypeManager::BOOLEAN, aCode->first()),
			AVMCODE_COMPILER.decode_compileStatement(aCTX, aCode->second()) );

	if( aCode->isOpCode( AVM_OPCODE_IFE ) )
	{
		aCompiledCode->append(
				AVMCODE_COMPILER.decode_compileStatement(
						aCTX, aCode->operand(2) ) );
	}

	return( aCompiledCode );
}


BFCode AvmcodeIteCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode optimizedCode( aCode->getOperator(),
			AVMCODE_COMPILER.decode_optimizeExpression(aCTX, aCode->first()),
			AVMCODE_COMPILER.decode_optimizeStatement(aCTX, aCode->second()) );

	AvmInstruction * argsInstruction =
			optimizedCode->newInstruction( aCode->size() );

	argsInstruction->at(0).dtype = TypeManager::BOOLEAN;
	setArgcodeRValue(aCTX, argsInstruction->at(0), optimizedCode->first());

	setArgcodeStatement(aCTX, argsInstruction->at(1), optimizedCode->second());

	if( aCode->isOpCode( AVM_OPCODE_IFE ) )
	{
		optimizedCode->append( AVMCODE_COMPILER.decode_optimizeStatement(
				aCTX, aCode->operand(2)) );

		setArgcodeStatement(aCTX,
				argsInstruction->at(2), optimizedCode->operand(2));
	}

	argsInstruction->computeMainBytecode(
			/*context  */ AVM_ARG_STANDARD_CTX,
			/*processor*/ AVM_ARG_STATEMENT_CPU,
			/*operation*/ AVM_ARG_SEVAL_RVALUE,
			/*operand  */ AVM_ARG_STATEMENT_KIND);

	return( optimizedCode );
}



} /* namespace sep */
