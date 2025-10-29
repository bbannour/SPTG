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

#include "AvmcodeQueueCompiler.h"

#include <fml/expression/AvmCode.h>
#include <fml/expression/ExpressionTypeChecker.h>

#include <fml/type/TypeManager.h>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
// AVMCODE PUSH COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodePushCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( compileStatement(aCTX, aCode) );
}

BF AvmcodePushCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( optimizeStatement(aCTX, aCode) );
}

BFCode AvmcodePushCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( compileExpressionCode(aCTX, aCode) );
}

BFCode AvmcodePushCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	AvmCode::iterator itOperand = aCode->begin();
	AvmCode::iterator endOperand = aCode->end();
	BFCode optimizedCode( aCode->getOperator() );

	AvmInstruction * argsInstruction =
			optimizedCode->newInstruction( aCode->size() );

	avm_arg_processor_t arg_cpu = AVM_ARG_STATEMENT_CPU;


	BF arg = AVMCODE_COMPILER.decode_optimizeExpression(aCTX, (*itOperand));
	optimizedCode->append( arg );

	setArgcodeContainerWValue(aCTX, argsInstruction->at(0), arg);

	if( argsInstruction->at(0).dtype->isTypedBuffer() )
	{
		arg = AVMCODE_COMPILER.decode_optimizeExpression(aCTX, (*(++itOperand)));
		optimizedCode->append( arg );

		if( ExpressionTypeChecker::isTyped(TypeManager::MESSAGE, arg) )
		{
			argsInstruction->at(1).dtype = TypeManager::MESSAGE;
			setArgcodeRValue(aCTX, argsInstruction->at(1), arg, false);
		}
		else if( ExpressionTypeChecker::isTyped(TypeManager::PORT, arg) )
		{
			argsInstruction->at(1).dtype = TypeManager::PORT;
			setArgcodeRValue(aCTX, argsInstruction->at(1), arg, false);

			if( arg.is< InstanceOfPort >() )
			{
				const InstanceOfPort & aPort = arg.to< InstanceOfPort >();
				std::size_t paramCount = aPort.getParameterCount();

				for( std::size_t offset = 2 ;
					(++itOperand != endOperand) && (offset <= paramCount) ;
					++offset )
				{
					arg = AVMCODE_COMPILER.
							decode_optimizeExpression(aCTX, (*itOperand));
					optimizedCode->append( arg );

					argsInstruction->at(offset).dtype =
							&( aPort.getParameterType(offset-1) );

					setArgcodeRValue(aCTX, argsInstruction->at(offset), arg);
				}
			}
			else for( std::size_t offset = 2 ;
					(++itOperand != endOperand) ; ++offset )
			{
				arg = AVMCODE_COMPILER.
						decode_optimizeExpression(aCTX, (*itOperand));
				optimizedCode->append( arg );

				argsInstruction->at(offset).dtype = TypeManager::UNIVERSAL;
				setArgcodeRValue(aCTX,
						argsInstruction->at(offset), (*itOperand), false);
			}
		}
		else for( std::size_t offset = 2 ;
				(++itOperand != endOperand) ; ++offset )
		{
			arg = AVMCODE_COMPILER.decode_optimizeExpression(aCTX, (*itOperand));
			optimizedCode->append( arg );

			argsInstruction->at(offset).dtype = TypeManager::UNIVERSAL;
			setArgcodeRValue(aCTX,
					argsInstruction->at(offset), (*itOperand), false);
		}
	}

	else if( argsInstruction->at(0).dtype->hasTypeCollection() )
	{
		arg_cpu = argsInstruction->at(0).dtype->hasTypeVector() ?
				AVM_ARG_VECTOR_CPU : AVM_ARG_COLLECTION_CPU;

		const BaseTypeSpecifier & aTS = argsInstruction->at(0).dtype
				->as< ContainerTypeSpecifier >().getContentsTypeSpecifier();

		for( avm_offset_t offset = 1 ; (++itOperand != endOperand) ; ++offset )
		{
			arg = AVMCODE_COMPILER.decode_optimizeExpression(
					aCTX->clone(aTS), (*itOperand));
			optimizedCode->append( arg );

			argsInstruction->at(offset).dtype = (& aTS);
			setArgcodeRValue(aCTX, argsInstruction->at(offset), arg);
		}
	}


	argsInstruction->computeMainBytecode(
			/*context  */ AVM_ARG_STANDARD_CTX,
			/*processor*/ arg_cpu,
			/*operation*/ AVM_ARG_SEVAL_RVALUE,
			/*operand  */ AVM_ARG_STATEMENT_KIND,
			/*dtype    */ argsInstruction->at(0).dtype);

	return( optimizedCode );
}



////////////////////////////////////////////////////////////////////////////////
// AVMCODE TOP COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeAssignTopCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( compileStatement(aCTX, aCode) );
}

BF AvmcodeAssignTopCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode optCode = optimizeStatement(aCTX, aCode);

	optCode->getInstruction()->setMainOperand( AVM_ARG_EXPRESSION_KIND );

	return( optCode );
}


BFCode AvmcodeAssignTopCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( compileExpressionCode(aCTX, aCode) );
}

BFCode AvmcodeAssignTopCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	AvmCode::iterator itOperand = aCode->begin();
	AvmCode::iterator endOperand = aCode->end();
	BFCode optimizedCode( aCode->getOperator() );

	AvmInstruction * argsInstruction =
			optimizedCode->newInstruction( aCode->size() );

	BF arg = AVMCODE_COMPILER.decode_optimizeExpression(aCTX, (*itOperand));
	optimizedCode->append( arg );

	setArgcodeContainerWValue(aCTX, argsInstruction->at(0), arg);

	if( argsInstruction->at(0).dtype->isTypedBuffer() )
	{
		arg = AVMCODE_COMPILER.decode_optimizeExpression(aCTX, (*(++itOperand)));
		optimizedCode->append( arg );

		if( ExpressionTypeChecker::isTyped(TypeManager::MESSAGE, arg) )
		{
			argsInstruction->at(1).dtype = TypeManager::MESSAGE;
			setArgcodeRValue(aCTX, argsInstruction->at(1), arg, false);
		}
		else if( ExpressionTypeChecker::isTyped(TypeManager::PORT, arg) )
		{
			argsInstruction->at(1).dtype = TypeManager::PORT;
			setArgcodeRValue(aCTX, argsInstruction->at(1), arg, false);

			if( arg.is< InstanceOfPort >() )
			{
				const InstanceOfPort & aPort = arg.to< InstanceOfPort >();
				std::size_t paramCount = aPort.getParameterCount();

				for( std::size_t offset = 2 ;
					(++itOperand != endOperand) && (offset <= paramCount) ;
					++offset )
				{
					arg = AVMCODE_COMPILER.
							decode_optimizeExpression(aCTX, (*itOperand));
					optimizedCode->append( arg );

					argsInstruction->at(offset).dtype =
							&( aPort.getParameterType(offset-1) );

					setArgcodeLValue(aCTX, argsInstruction->at(offset), arg);
				}
			}
			else for( std::size_t offset = 2 ;
					(++itOperand != endOperand) ; ++offset )
			{
				arg = AVMCODE_COMPILER.
						decode_optimizeExpression(aCTX, (*itOperand));
				optimizedCode->append( arg );

				argsInstruction->at(offset).dtype = TypeManager::UNIVERSAL;
				setArgcodeLValue(aCTX,
						argsInstruction->at(offset), (*itOperand), false);
			}
		}
		else for( std::size_t offset = 2 ; (++itOperand != endOperand) ; ++offset )
		{
			arg = AVMCODE_COMPILER.decode_optimizeExpression(aCTX, (*itOperand));
			optimizedCode->append( arg );

			argsInstruction->at(offset).dtype = TypeManager::UNIVERSAL;
			setArgcodeLValue(aCTX,
					argsInstruction->at(offset), (*itOperand), false);
		}
	}

	else if( argsInstruction->at(0).dtype->hasTypeCollection() )
	{
		const BaseTypeSpecifier & aTS = argsInstruction->at(0).dtype
				->as< ContainerTypeSpecifier >().getContentsTypeSpecifier();

		for( avm_offset_t offset = 1 ; (++itOperand != endOperand) ; ++offset )
		{
			arg = AVMCODE_COMPILER.decode_optimizeExpression(
					aCTX->clone(aTS), (*itOperand));
			optimizedCode->append( arg );

			argsInstruction->at(offset).dtype = (& aTS);
			setArgcodeRValue(aCTX, argsInstruction->at(offset), arg);
		}
	}


	argsInstruction->computeMainBytecode(
			/*context  */ AVM_ARG_STANDARD_CTX,
			/*processor*/ AVM_ARG_STATEMENT_CPU,
			/*operation*/ AVM_ARG_SEVAL_RVALUE,
			/*operand  */ AVM_ARG_STATEMENT_KIND,
			/*dtype    */ argsInstruction->at(0).dtype);

	return( optimizedCode );
}



////////////////////////////////////////////////////////////////////////////////
// AVMCODE TOP COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeTopCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( compileExpressionCode(aCTX, aCode) );
}

BF AvmcodeTopCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode optCode = optimizeExpressionCode(aCTX, aCode, AVM_ARG_EXPRESSION_KIND) ;

	optCode->getInstruction()->setMainProcessor( AVM_ARG_QUEUE_CPU );

	return( optCode );
}


BFCode AvmcodeTopCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( compileExpressionCode(aCTX, aCode) );
}

BFCode AvmcodeTopCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( optimizeStatementCode(aCTX, aCode) );
}



////////////////////////////////////////////////////////////////////////////////
// AVMCODE POP COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodePopCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( compileStatement(aCTX, aCode) );
}

BF AvmcodePopCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode optCode = optimizeStatement(aCTX, aCode);

	optCode->getInstruction()->setMainProcessor( AVM_ARG_QUEUE_CPU );
	optCode->getInstruction()->setMainOperand( AVM_ARG_EXPRESSION_KIND );

	return( optCode );
}


BFCode AvmcodePopCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( compileExpressionCode(aCTX, aCode) );
}

BFCode AvmcodePopCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	AvmCode::iterator itOperand = aCode->begin();
	AvmCode::iterator endOperand = aCode->end();
	BFCode optimizedCode( aCode->getOperator() );

	AvmInstruction * argsInstruction =
			optimizedCode->newInstruction( aCode->size() );

	BF arg = AVMCODE_COMPILER.decode_optimizeExpression(aCTX, (*itOperand));
	optimizedCode->append( arg );

	setArgcodeContainerWValue(aCTX, argsInstruction->at(0), arg);

	if( argsInstruction->at(0).dtype->isTypedBuffer() )
	{
		arg = AVMCODE_COMPILER.decode_optimizeExpression(aCTX, (*(++itOperand)));
		optimizedCode->append( arg );

		if( ExpressionTypeChecker::isTyped(TypeManager::MESSAGE, arg) )
		{
			argsInstruction->at(1).dtype = TypeManager::MESSAGE;
			setArgcodeRValue(aCTX, argsInstruction->at(1), arg, false);
		}
		else if( ExpressionTypeChecker::isTyped(TypeManager::PORT, arg) )
		{
			argsInstruction->at(1).dtype = TypeManager::PORT;
			setArgcodeRValue(aCTX, argsInstruction->at(1), arg, false);

			if( arg.is< InstanceOfPort >() )
			{
				const InstanceOfPort & aPort = arg.to< InstanceOfPort >();
				std::size_t paramCount = aPort.getParameterCount();

				for( std::size_t offset = 2 ;
					(++itOperand != endOperand) && (offset <= paramCount) ;
					++offset )
				{
					arg = AVMCODE_COMPILER.
							decode_optimizeExpression(aCTX, (*itOperand));
					optimizedCode->append( arg );

					argsInstruction->at(offset).dtype =
							&( aPort.getParameterType(offset-1) );

					setArgcodeLValue(aCTX, argsInstruction->at(offset), arg);
				}
			}
			else for( std::size_t offset = 2 ;
					(++itOperand != endOperand) ; ++offset )
			{
				arg = AVMCODE_COMPILER.
						decode_optimizeExpression(aCTX, (*itOperand));
				optimizedCode->append( arg );

				argsInstruction->at(offset).dtype = TypeManager::UNIVERSAL;
				setArgcodeLValue(aCTX,
						argsInstruction->at(offset), (*itOperand), false);
			}
		}
		else for( std::size_t offset = 2 ;
				(++itOperand != endOperand) ; ++offset )
		{
			arg = AVMCODE_COMPILER.decode_optimizeExpression(aCTX, (*itOperand));
			optimizedCode->append( arg );

			argsInstruction->at(offset).dtype = TypeManager::UNIVERSAL;
			setArgcodeLValue(aCTX,
					argsInstruction->at(offset), (*itOperand), false);
		}
	}

	else if( argsInstruction->at(0).dtype->hasTypeCollection() )
	{
		const BaseTypeSpecifier & aTS = argsInstruction->at(0).dtype
				->as_ptr< ContainerTypeSpecifier >()->getContentsTypeSpecifier();

		for( avm_offset_t offset = 1 ; (++itOperand != endOperand) ; ++offset )
		{
			arg = AVMCODE_COMPILER.decode_optimizeExpression(
					aCTX->clone(aTS), (*itOperand));
			optimizedCode->append( arg );

			argsInstruction->at(offset).dtype = (& aTS);
			setArgcodeLValue(aCTX, argsInstruction->at(offset), arg);
		}
	}


	argsInstruction->computeMainBytecode(
			/*context  */ AVM_ARG_STANDARD_CTX,
			/*processor*/ AVM_ARG_STATEMENT_CPU,
			/*operation*/ AVM_ARG_SEVAL_RVALUE,
			/*operand  */ AVM_ARG_STATEMENT_KIND,
			/*dtype    */ argsInstruction->at(0).dtype);

	return( optimizedCode );
}



////////////////////////////////////////////////////////////////////////////////
// AVMCODE POP_FROM COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodePopFromCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( compileStatement(aCTX, aCode) );
}

BF AvmcodePopFromCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode optCode = optimizeStatement(aCTX, aCode);

	optCode->getInstruction()->setMainProcessor( AVM_ARG_QUEUE_CPU );
	optCode->getInstruction()->setMainOperand( AVM_ARG_EXPRESSION_KIND );

	return( optCode );
}


BFCode AvmcodePopFromCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( compileExpressionCode(aCTX, aCode) );
}

BFCode AvmcodePopFromCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	AvmInstruction * argsInstruction = aCode->genInstruction();

	optimizeArgExpression(aCTX, aCode, 0);
	setArgcodeContainerWValue(aCTX,
			argsInstruction->at(0), aCode->first());

	if( argsInstruction->at(0).dtype->isTypedBuffer() )
	{
		//!!! TODO
		optimizeArgExpression(aCTX, aCode, 1);
		setArgcodeContainerRValue(aCTX,
				argsInstruction->at(1), aCode->second());
	}
	else if( argsInstruction->at(0).dtype->hasTypeCollection() )
	{
		optimizeArgExpression(aCTX, aCode, 1);
		setArgcodeContainerRValue(aCTX,
				argsInstruction->at(1), aCode->second());
	}


	argsInstruction->computeMainBytecode(
			/*context  */ AVM_ARG_STANDARD_CTX,
			/*processor*/ AVM_ARG_STATEMENT_CPU,
			/*operation*/ AVM_ARG_SEVAL_RVALUE,
			/*operand  */ AVM_ARG_STATEMENT_KIND,
			/*dtype    */ argsInstruction->at(0).dtype);

	return( aCode );
}




}

