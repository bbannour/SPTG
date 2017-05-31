/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 29 avr. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmcodeMathFunctionCompiler.h"

#include <fml/type/TypeManager.h>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
// AVMCODE ARITHMETIC EXPRESSION COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeMathFunctionCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( compileExpressionCode(aCTX, aCode) );
}

BF AvmcodeMathFunctionCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode optCode = optimizeExpressionCode(aCTX, aCode, AVM_ARG_EXPRESSION_KIND) ;

	optCode->getInstruction()->setMainBytecode(
			/*context  */ AVM_ARG_RETURN_CTX,
			/*processor*/ AVM_ARG_ARITHMETIC_LOGIC_CPU,
			/*operation*/ AVM_ARG_SEVAL_RVALUE,
			/*operand  */ AVM_ARG_EXPRESSION_KIND,
			/*dtype    */ TypeManager::UNIVERSAL );


	return( optCode );
}


}
