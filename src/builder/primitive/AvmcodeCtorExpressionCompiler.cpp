/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 12 avr. 2013
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmcodeCtorExpressionCompiler.h"

#include <fml/expression/BuiltinArray.h>
#include <fml/expression/ExpressionConstructor.h>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
// AVMCODE CTOR EXPRESSION COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeCtorExpressionCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BF ctorType = compileArgRvalue(aCTX, aCode->first());
	if( not ctorType.is< BaseTypeSpecifier >() )
	{
		getCompilerTable().incrErrorCount();
		aCTX->errorContext( AVM_OS_WARN )
				<< "AvmcodeCtorExpressionCompiler::compileExpression :> "
					"Unexpected <<" << str_indent( ctorType )
				<< " >> as a type specifier of ctor expression :"
				<< IGNORE_FIRST_TAB << aCode
				<< std::endl;

		return( aCode );
	}

	const BaseTypeSpecifier & ctorTypeSpecifier =
			ctorType.as< BaseTypeSpecifier >();

	BF bfExpr = aCode->second();

	if( bfExpr.is< BuiltinArray >()
		&& ctorTypeSpecifier.hasTypeComposite() )
	{
		bfExpr = compileArgRvalue(aCTX->clone(ctorTypeSpecifier), bfExpr);

		if( bfExpr.to< BuiltinArray >().
				getTypeSpecifier().isTEQ( ctorTypeSpecifier ) )
		{
			return( bfExpr );
		}

		return( ExpressionConstructor::newCode(
				aCode->getOperator(), ctorType, bfExpr) );
	}
	else
	{
		return( ExpressionConstructor::newCode(
				aCode->getOperator(), ctorType,
				compileArgRvalue(aCTX, bfExpr, false) ) );
	}
}

BF AvmcodeCtorExpressionCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	AvmInstruction * argsInstruction = aCode->genInstruction();

	argsInstruction->set(0,
			/*context  */ AVM_ARG_STANDARD_CTX,
			/*processor*/ AVM_ARG_NOP_CPU,
			/*operation*/ AVM_ARG_NOP_VALUE,
			/*operand  */ AVM_ARG_CTOR_TYPE_KIND,
			/*type     */ aCode->first().as< BaseTypeSpecifier >() );

	optimizeArgExpression(aCTX, aCode, 1);
	argsInstruction->at(1).dtype = aCode->first().to_ptr< BaseTypeSpecifier >();
	setArgcodeRValue(aCTX, argsInstruction->at(1), aCode->second(), false);

	avm_arg_processor_t mainProcessor =
			processorOf(* argsInstruction->dtype(0) );

	switch( argsInstruction->operand(1) )
	{
		case AVM_ARG_STRING_KIND:
		case AVM_ARG_ENUM_LITERAL_KIND:
		{
			mainProcessor = argsInstruction->at(1).dtype->isTypedEnum() ?
					AVM_ARG_STRING_CPU : AVM_ARG_STRING_CPU;
			break;
		}
		case AVM_ARG_CHARACTER_KIND:
		{
			mainProcessor = argsInstruction->at(1).dtype->isTypedEnum() ?
					AVM_ARG_STRING_CPU : AVM_ARG_CHARACTER_CPU;
			break;
		}
		case AVM_ARG_BOOLEAN_KIND:
		case AVM_ARG_INTEGER_KIND:
		case AVM_ARG_RATIONAL_KIND:
		case AVM_ARG_FLOAT_KIND:
		{
			mainProcessor = argsInstruction->at(1).dtype->isTypedEnum() ?
					AVM_ARG_STRING_CPU : AVM_ARG_ARITHMETIC_LOGIC_CPU;
			break;
		}

		case AVM_ARG_ARRAY_KIND:
		{
			mainProcessor = AVM_ARG_COLLECTION_CPU;
			break;
		}

		default:
		{
			if( argsInstruction->dtype(1) != TypeManager::UNIVERSAL )
			{
				mainProcessor = processorOf(* argsInstruction->dtype(1) );
			}
			break;
		}
	}

	argsInstruction->setMainBytecode(
			/*context  */ AVM_ARG_RETURN_CTX,
			/*processor*/ mainProcessor,
			/*operation*/ AVM_ARG_SEVAL_RVALUE,
			/*operand  */ operandOf(* argsInstruction->dtype(0) ),
			/*dtype    */ argsInstruction->dtype(0) );

	return( aCode );
}



} /* namespace sep */
