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

#include "AvmcodeMachineStatusCompiler.h"

#include <fml/expression/AvmCode.h>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
// AVMCODE MACHINE STATUS EXPRESSION COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeMachineStatusExpressionCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode aCompiledCode( aCode->getOperator(),
			compileArgRvalue(aCTX, TypeManager::OPERATOR, aCode->first()),
			compileArgRvalue(aCTX, TypeManager::MACHINE , aCode->second()) );

	return( aCompiledCode );
}


BF AvmcodeMachineStatusExpressionCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	AvmInstruction * argsInstruction = aCode->genInstruction();

	optimizeArgExpression(aCTX, aCode, 0);
	optimizeArgExpression(aCTX, aCode, 1);

	if( aCode->first().isnot< Operator >() && aCode->second().is< Operator >() )
	{
		std::swap(aCode->first(), aCode->second());
	}

	argsInstruction->at(0).dtype = TypeManager::OPERATOR;
	setArgcodeRValue(aCTX, argsInstruction->at(0), aCode->first());

	argsInstruction->at(1).dtype = TypeManager::MACHINE;
	setArgcodeRValue(aCTX, argsInstruction->at(1), aCode->second());

	argsInstruction->computeMainBytecode(
			/*context  */ AVM_ARG_RETURN_CTX,
			/*processor*/ AVM_ARG_MEMORY_MACHINE_CPU,
			/*operation*/ AVM_ARG_SEVAL_RVALUE,
			/*operand  */ AVM_ARG_EXPRESSION_KIND,
			/*dtype    */ TypeManager::BOOLEAN);

	return( aCode );
}


}
