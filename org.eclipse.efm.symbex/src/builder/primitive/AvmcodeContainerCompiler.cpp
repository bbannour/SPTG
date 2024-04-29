/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 12 avr. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmcodeContainerCompiler.h"

#include <fml/expression/AvmCode.h>
#include <fml/expression/ExpressionTypeChecker.h>
#include <fml/expression/StatementConstructor.h>

#include <fml/operator/OperatorLib.h>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
// AVMCODE CONTAINER UNARY STATEMENT COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeUnaryContainerStatementCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( compileStatement(aCTX, aCode) );
}

BF AvmcodeUnaryContainerStatementCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	AvmInstruction * argsInstruction = aCode->genInstruction();

	optimizeArgExpression(aCTX, aCode, 0);
	argsInstruction->at(0).dtype = TypeManager::UNIVERSAL;
	setArgcodeContainerRValue(aCTX, argsInstruction->at(0), aCode->first());

	avm_arg_processor_t arg_cpu =
			aCode->first().is< InstanceOfBuffer >()
					? AVM_ARG_BUFFER_CPU
					: ExpressionTypeChecker::isVector( aCode->first() )
							? AVM_ARG_VECTOR_CPU
							: AVM_ARG_COLLECTION_CPU;

	argsInstruction->computeMainBytecode(
			/*context  */ AVM_ARG_STANDARD_CTX,
			/*processor*/ arg_cpu,
			/*operation*/ AVM_ARG_SEVAL_RVALUE,
			/*operand  */ AVM_ARG_EXPRESSION_KIND,
			/*dtype    */ argsInstruction->at(0).dtype);

	return( aCode );
}


BFCode AvmcodeUnaryContainerStatementCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BF container = compileArgRvalue(aCTX, TypeManager::UNIVERSAL, aCode->first());

	return( StatementConstructor::newCode(aCode->getOperator(), container) );
}

BFCode AvmcodeUnaryContainerStatementCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	AvmInstruction * argsInstruction = aCode->genInstruction();

	optimizeArgExpression(aCTX, aCode, 0);
	argsInstruction->at(0).dtype = TypeManager::UNIVERSAL;
	setArgcodeContainerRValue(aCTX, argsInstruction->at(0), aCode->first());

	argsInstruction->computeMainBytecode(
			/*context  */ AVM_ARG_STANDARD_CTX,
			/*processor*/ AVM_ARG_STATEMENT_CPU,
			/*operation*/ AVM_ARG_SEVAL_RVALUE,
			/*operand  */ AVM_ARG_STATEMENT_KIND,
			/*dtype    */ argsInstruction->at(0).dtype);

	return( aCode );
}


////////////////////////////////////////////////////////////////////////////////
// AVMCODE WRITE CONTAINER UNARY STATEMENT COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeUnaryWriteContainerStatementCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( compileStatement(aCTX, aCode) );
}

BF AvmcodeUnaryWriteContainerStatementCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode optCode = optimizeStatement(aCTX, aCode);

	avm_arg_processor_t arg_cpu =
			ExpressionTypeChecker::isVector( aCode->first() ) ?
					AVM_ARG_VECTOR_CPU : AVM_ARG_COLLECTION_CPU;

	optCode->getInstruction()->setMainProcessor( arg_cpu );
	optCode->getInstruction()->setMainOperand( AVM_ARG_EXPRESSION_KIND );

	return( optCode );
}


BFCode AvmcodeUnaryWriteContainerStatementCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BF container = compileArgRvalue(aCTX, TypeManager::UNIVERSAL, aCode->first());

	return( StatementConstructor::newCode(aCode->getOperator(), container) );
}

BFCode AvmcodeUnaryWriteContainerStatementCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	AvmInstruction * argsInstruction = aCode->genInstruction();

	optimizeArgExpression(aCTX, aCode, 0);
	argsInstruction->at(0).dtype = TypeManager::UNIVERSAL;
	setArgcodeContainerWValue(aCTX, argsInstruction->at(0), aCode->first());

	argsInstruction->computeMainBytecode(
			/*context  */ AVM_ARG_STANDARD_CTX,
			/*processor*/ AVM_ARG_STATEMENT_CPU,
			/*operation*/ AVM_ARG_SEVAL_RVALUE,
			/*operand  */ AVM_ARG_STATEMENT_KIND,
			/*dtype    */ argsInstruction->at(0).dtype);

	return( aCode );
}



////////////////////////////////////////////////////////////////////////////////
// AVMCODE CONTAINER BINARY STATEMENT COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeBinaryContainerStatementCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( compileStatement(aCTX, aCode) );
}

BF AvmcodeBinaryContainerStatementCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode optCode = optimizeStatement(aCTX, aCode);

	BF optContainer = optCode->hasOpCode(AVM_OPCODE_IN, AVM_OPCODE_NOTIN) ?
			aCode->second() : aCode->first();

	avm_arg_processor_t arg_cpu =
			ExpressionTypeChecker::isVector( optContainer ) ?
					AVM_ARG_VECTOR_CPU : AVM_ARG_COLLECTION_CPU;

	optCode->getInstruction()->setMainProcessor( arg_cpu );
	optCode->getInstruction()->setMainOperand( AVM_ARG_EXPRESSION_KIND );

	return( optCode );
}


BFCode AvmcodeBinaryContainerStatementCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BF container;
	BF element;
	if( aCode->hasOpCode(AVM_OPCODE_IN, AVM_OPCODE_NOTIN) )
	{
		container = aCode->second();
		element   = aCode->first();
	}
	else
	{
		container = aCode->first();
		element   = aCode->second();
	}

	container = compileArgRvalue(aCTX, TypeManager::UNIVERSAL, container);

	bool requestTypeChecking = false;

	if( container.is< InstanceOfData >() )
	{
		InstanceOfData * anInstance = container.to_ptr< InstanceOfData >();
		if( anInstance->hasTypeContainer()
			&& aCode->hasOpCode(AVM_OPCODE_CONTAINS,
					AVM_OPCODE_IN, AVM_OPCODE_NOTIN) )
		{
			aCTX = aCTX->clone( anInstance->getTypeSpecifier().
					to< ContainerTypeSpecifier >().getContentsTypeSpecifier() );

			requestTypeChecking = true;
		}
	}
	else if( container.is< ArrayBF >() )
	{
		ArrayBF * anArray = container.to_ptr< ArrayBF >();
		if( anArray->hasTypeSpecifier() )
		{
			aCTX = aCTX->clone( anArray->getTypeSpecifier() );

			requestTypeChecking = true;
		}
	}

	element = compileArgRvalue(aCTX, element, requestTypeChecking);


	if( aCode->hasOpCode(AVM_OPCODE_IN, AVM_OPCODE_NOTIN) )
	{
		return( StatementConstructor::newCode(
				aCode->getOperator(), element, container) );
	}
	else
	{
		return( StatementConstructor::newCode(
				aCode->getOperator(), container, element) );
	}
}

BFCode AvmcodeBinaryContainerStatementCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	AvmInstruction * argsInstruction = aCode->genInstruction();

	argsInstruction->at(0).dtype = TypeManager::UNIVERSAL;
	setArgcodeRValue(aCTX, argsInstruction->at(0), aCode->first(), false);

	argsInstruction->at(1).dtype = TypeManager::UNIVERSAL;
	setArgcodeRValue(aCTX, argsInstruction->at(1), aCode->second(), false);

	argsInstruction->computeMainBytecode(
			/*context  */ AVM_ARG_STANDARD_CTX,
			/*processor*/ AVM_ARG_STATEMENT_CPU,
			/*operation*/ AVM_ARG_SEVAL_RVALUE,
			/*operand  */ AVM_ARG_STATEMENT_KIND,
			/*dtype    */ argsInstruction->at(0).dtype);

	return( aCode );
}


////////////////////////////////////////////////////////////////////////////////
// AVMCODE WRITE CONTAINER BINARY STATEMENT COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeBinaryWriteContainerStatementCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( compileStatement(aCTX, aCode) );
}

BF AvmcodeBinaryWriteContainerStatementCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode optCode = optimizeStatement(aCTX, aCode);

	BF optContainer = optCode->hasOpCode(AVM_OPCODE_IN, AVM_OPCODE_NOTIN) ?
			aCode->second() : aCode->first();

	avm_arg_processor_t arg_cpu =
			ExpressionTypeChecker::isVector( optContainer ) ?
					AVM_ARG_VECTOR_CPU : AVM_ARG_COLLECTION_CPU;

	optCode->getInstruction()->setMainProcessor( arg_cpu );
	optCode->getInstruction()->setMainOperand( AVM_ARG_EXPRESSION_KIND );

	return( optCode );
}


BFCode AvmcodeBinaryWriteContainerStatementCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BF container = compileArgRvalue(aCTX, TypeManager::UNIVERSAL, aCode->first());

	InstanceOfData * instance = nullptr;
	if( container.is< InstanceOfData >() )
	{
		instance = container.to_ptr< InstanceOfData >();
		if( instance->hasTypeContainer() )
		{
			if( aCode->hasOpCode(AVM_OPCODE_APPEND, AVM_OPCODE_REMOVE) )
			{
				aCTX = aCTX->clone( instance->getTypeSpecifier().
					to< ContainerTypeSpecifier >().getContentsTypeSpecifier() );
			}
			else if( aCode->isOpCode(AVM_OPCODE_RESIZE) )
			{
				aCTX = aCTX->clone( TypeManager::INTEGER );
			}
		}
	}

	BF element = compileArgRvalue(aCTX, aCode->second(), true);

	return( StatementConstructor::newCode(
			aCode->getOperator(), container, element) );
}

BFCode AvmcodeBinaryWriteContainerStatementCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	AvmInstruction * argsInstruction = aCode->genInstruction();

	argsInstruction->at(0).dtype = TypeManager::UNIVERSAL;
	setArgcodeContainerWValue(aCTX, argsInstruction->at(0), aCode->first());

	argsInstruction->at(1).dtype = TypeManager::UNIVERSAL;
	setArgcodeRValue(aCTX, argsInstruction->at(1), aCode->second(), false);

	argsInstruction->computeMainBytecode(
			/*context  */ AVM_ARG_STANDARD_CTX,
			/*processor*/ AVM_ARG_STATEMENT_CPU,
			/*operation*/ AVM_ARG_SEVAL_RVALUE,
			/*operand  */ AVM_ARG_STATEMENT_KIND,
			/*dtype    */ argsInstruction->at(0).dtype);

	return( aCode );
}



}
