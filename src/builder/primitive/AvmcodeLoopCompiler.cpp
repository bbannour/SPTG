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

#include "AvmcodeLoopCompiler.h"

#include <builder/primitive/AvmcodeCompiler.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/StatementConstructor.h>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
// AVMCODE FOR COMPILATION
////////////////////////////////////////////////////////////////////////////////

BFCode AvmcodeForCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( StatementConstructor::newCode(aCode->getOperator(),
			AVMCODE_COMPILER.decode_compileStatement(aCTX, aCode->first()),
			compileArgRvalue(aCTX, TypeManager::BOOLEAN, aCode->second()),
			AVMCODE_COMPILER.decode_compileStatement(aCTX, aCode->operand(2)),
			AVMCODE_COMPILER.decode_compileStatement(aCTX, aCode->operand(3))) );
}


BFCode AvmcodeForCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode optimizedCode(aCode->getOperator(),
			AVMCODE_COMPILER.decode_optimizeStatement(aCTX, aCode->first()),
			AVMCODE_COMPILER.decode_optimizeExpression(aCTX, aCode->second()),
			AVMCODE_COMPILER.decode_optimizeStatement(aCTX, aCode->operand(2)),
			AVMCODE_COMPILER.decode_optimizeStatement(aCTX, aCode->operand(3)) );

	AvmInstruction * argsInstruction = optimizedCode->genInstruction();

	setArgcodeStatement(aCTX, argsInstruction->at(0), optimizedCode->first());

	argsInstruction->at(1).dtype = TypeManager::BOOLEAN;
	setArgcodeRValue(aCTX, argsInstruction->at(1), optimizedCode->second());

	setArgcodeStatement(aCTX, argsInstruction->at(2), optimizedCode->operand(2));

	setArgcodeStatement(aCTX, argsInstruction->at(3), optimizedCode->operand(3));

	argsInstruction->setMainBytecode(
			/*operation*/ AVM_ARG_NOPS,
			/*operand  */ AVM_ARG_STATEMENT_KIND );

	return( optimizedCode );
}


////////////////////////////////////////////////////////////////////////////////
// AVMCODE FOREACH COMPILATION
////////////////////////////////////////////////////////////////////////////////

BFCode AvmcodeForeachCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( StatementConstructor::newCode( aCode->getOperator(),
			compileArgLvalue(aCTX, aCode->first()),
			compileArgRvalue(aCTX, aCode->second()),
			AVMCODE_COMPILER.decode_compileStatement(aCTX, aCode->operand(2)) ) );
}


BFCode AvmcodeForeachCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode optimizedCode(aCode->getOperator(),
			AVMCODE_COMPILER.decode_optimizeExpression(aCTX, aCode->first()),
			AVMCODE_COMPILER.decode_optimizeExpression(aCTX, aCode->second()),
			AVMCODE_COMPILER.decode_optimizeStatement(aCTX, aCode->operand(2)) );

	AvmInstruction * argsInstruction = optimizedCode->genInstruction();

	setArgcodeLValue(aCTX, argsInstruction->at(0), optimizedCode->first(), false);

	setArgcodeRValue(aCTX, argsInstruction->at(1), optimizedCode->second());

	setArgcodeStatement(aCTX, argsInstruction->at(2), optimizedCode->operand(2));

	argsInstruction->computeMainBytecode(
			/*context  */ AVM_ARG_STANDARD_CTX,
			/*processor*/ AVM_ARG_STATEMENT_CPU,
			/*operation*/ AVM_ARG_SEVAL_VALUE,
			/*operand  */ AVM_ARG_STATEMENT_KIND);

	return( optimizedCode );
}


////////////////////////////////////////////////////////////////////////////////
// AVMCODE WHILE DO COMPILATION
////////////////////////////////////////////////////////////////////////////////

BFCode AvmcodeWhileDoCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( StatementConstructor::newCode(aCode->getOperator(),
			compileArgRvalue(aCTX, TypeManager::BOOLEAN, aCode->first()),
			AVMCODE_COMPILER.decode_compileStatement(aCTX, aCode->second())) );
}


BFCode AvmcodeWhileDoCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode optimizedCode(StatementConstructor::newCode(aCode->getOperator(),
			AVMCODE_COMPILER.decode_optimizeExpression(aCTX, aCode->first()),
			AVMCODE_COMPILER.decode_optimizeStatement(aCTX, aCode->second())) );

	AvmInstruction * argsInstruction = optimizedCode->genInstruction();

	argsInstruction->at(0).dtype = TypeManager::BOOLEAN;
	setArgcodeRValue(aCTX, argsInstruction->at(0), optimizedCode->first());

	setArgcodeStatement(aCTX, argsInstruction->at(1), optimizedCode->second());

	argsInstruction->setMainBytecode(
			/*operation*/ AVM_ARG_NOPS,
			/*operand  */ AVM_ARG_STATEMENT_KIND );

	return( optimizedCode );
}


////////////////////////////////////////////////////////////////////////////////
// AVMCODE DO WHILE COMPILATION
////////////////////////////////////////////////////////////////////////////////

BFCode AvmcodeDoWhileCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( StatementConstructor::newCode(aCode->getOperator(),
			AVMCODE_COMPILER.decode_compileStatement(aCTX, aCode->first()),
			compileArgRvalue(aCTX, TypeManager::BOOLEAN, aCode->second())) );
}


BFCode AvmcodeDoWhileCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode optimizedCode(StatementConstructor::newCode(aCode->getOperator(),
			AVMCODE_COMPILER.decode_optimizeStatement(aCTX, aCode->first()),
			AVMCODE_COMPILER.decode_optimizeExpression(aCTX, aCode->second())) );

	AvmInstruction * argsInstruction = optimizedCode->genInstruction();

	setArgcodeStatement(aCTX, argsInstruction->at(0), optimizedCode->first());

	argsInstruction->at(1).dtype = TypeManager::BOOLEAN;
	setArgcodeRValue(aCTX, argsInstruction->at(1), optimizedCode->second());

	argsInstruction->setMainBytecode(
			/*operation*/ AVM_ARG_NOPS,
			/*operand  */ AVM_ARG_STATEMENT_KIND );

	return( optimizedCode );
}


} /* namespace sep */
