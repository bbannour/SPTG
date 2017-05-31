/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 16 avr. 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "InstructionEnvironment.h"

#include <sstream>

#include <builder/Builder.h>

#include <computer/BaseEnvironment.h>
#include <computer/EvaluationEnvironment.h>
#include <computer/ExecutionDataFactory.h>

#include <computer/instruction/AvmInstruction.h>

#include <fml/buffer/BaseBufferForm.h>

#include <fml/executable/ExecutableLib.h>
#include <fml/executable/InstanceOfBuffer.h>
#include <fml/executable/InstanceOfConnect.h>
#include <fml/executable/InstanceOfData.h>
#include <fml/executable/InstanceOfMachine.h>
#include <fml/executable/InstanceOfPort.h>

#include <fml/operator/Operator.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/BuiltinArray.h>
#include <fml/expression/BuiltinQueue.h>
#include <fml/builtin/Character.h>
#include <fml/expression/ExpressionComparer.h>
#include <fml/expression/ExpressionConstructor.h>
#include <fml/expression/ExpressionConstructorImpl.h>
#include <fml/expression/StatementFactory.h>
#include <fml/builtin/String.h>

#include <fml/runtime/ExecutionConfiguration.h>
#include <fml/runtime/LocalRuntime.h>
#include <fml/runtime/RuntimeLib.h>

#include <fml/type/ContainerTypeSpecifier.h>


namespace sep
{


/**
 * CONSTRUCTOR
 * Default
 */
InstructionEnvironment::InstructionEnvironment(BaseEnvironment & ENV)
: AvmObject( ),
mARG( newARGS(&ENV, ENV.inED, ENV.inCODE->size()) ),
itARG( mARG )
{
	//!! NOTHING
}

InstructionEnvironment::InstructionEnvironment(
		BaseEnvironment & ENV, avm_size_t count)
: AvmObject( ),
mARG( newARGS(&ENV, ENV.inED, count) ),
itARG( mARG )
{
	//!! NOTHING
}


///////////////////////////////////////////////////////////////////////////
// CACHE MANAGER
///////////////////////////////////////////////////////////////////////////

List< ARGS_ENV * >  InstructionEnvironment::ARGS_ENV_CACHE;


void InstructionEnvironment::initCache()
{
	for( avm_size_t offset = 0 ;
			offset < ARGS_ENV_INITIAL_CACHE_COUNT ; ++offset )
	{
		ARGS_ENV_CACHE.append( new ARGS_ENV(NULL, APExecutionData::REF_NULL,
				ARGS_ENV_DEFAULT_CAPACITY, 0) );
	}
}


void InstructionEnvironment::finalizeCache()
{
	avm_size_t finalCacheSize = 0;

	while( ARGS_ENV_CACHE.nonempty() )
	{
//AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
//		AVM_OS_TRACE << "ARGS_ENV::finalize:> @"
//				<< avm_address_t( ARGS_ENV_CACHE.last() ) << std::endl;
//AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )

		++finalCacheSize;
		delete( ARGS_ENV_CACHE.pop_last() );
	}

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , STATEMENT )
	AVM_OS_TRACE << "ARGS_ENV::finalize#cache:> count = " << finalCacheSize
			<< std::endl;

	AVM_OS_TRACE << "ARGS_ENV::CALL:> count = "
			<< ARGS_ENV::CALL_COUNT << std::endl
			<< "ARGS_ENV::CALL<GiNaC:> count = "
			<< ARGS_ENV::CALL_COUNT_GINAC << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , STATEMENT )
}


ARGS_ENV * InstructionEnvironment::newARGS(BaseEnvironment * ENV,
		const APExecutionData & anED, avm_size_t count)
{
	ARGS_ENV * arg = NULL;

	if( ARGS_ENV_CACHE.nonempty() &&
		(ARGS_ENV_CACHE.last()->capacity > count) )
	{
		ARGS_ENV_CACHE.pop_last_to( arg );

		arg->ENV = ENV;
		arg->outED = anED;

		arg->table.resize( arg->count = count );
		arg->values = & ( arg->table );

		arg->idx = 0;
		arg->NEXT = NULL;
	}
	else
	{
		arg = new ARGS_ENV(ENV, anED, count + ARGS_ENV_INCR_CAPACITY, count);

		AVM_OS_ASSERT_OUT_OF_MEMORY_EXIT( arg )
				<< "BaseEnvironment::newARGS !!!"
				<< SEND_EXIT;
	}

//AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
//	AVM_OS_TRACE << "ARGS_ENV::new:> @" << avm_address_t( arg )
//			<< std::endl;
//AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )

	return( arg );
}


void InstructionEnvironment::freeARGS(ARGS_ENV * & arg)
{
	if( arg->NEXT == NULL )
	{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
		AVM_OS_TRACE << "ARGS_ENV::free:> @" << avm_address_t( arg )
				<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
		ARGS_ENV_CACHE.append( arg );
	}
	else
	{
		for( ARGS_ENV * nextArg = arg ; arg != NULL ; arg = nextArg )
		{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
			AVM_OS_TRACE << "ARGS_ENV::free:> @" << avm_address_t( arg )
					<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )

			nextArg = arg->NEXT;
			arg->NEXT = NULL;
			ARGS_ENV_CACHE.append( arg );
		}
	}

	arg = NULL;
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// 	 DECODE EVAL
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

avm_size_t  ARGS_ENV::CALL_COUNT = 0;

avm_size_t  ARGS_ENV::CALL_COUNT_GINAC = 0;



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// 	 DECODE EVAL CONTEXT
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool ARGS_ENV::main_decode_eval(BFCode & inCODE)
{
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( inCODE->hasInstruction() )
			<< "ARGS_ENV::main_decode_eval :> "
			"Unexpected a code without instruction !!!"
			<< SEND_EXIT;

	if( (argsInstruction = inCODE->getInstruction())->isNopCPU() )
	{
		current( inCODE );

		return( true );
	}
	else
	{
		argsBytecode = argsInstruction->getBytecode();

		return( decode_eval_processor( argsInstruction->getMainBytecode(),
				inCODE->to< AvmCode >() ) );
	}
}


bool ARGS_ENV::main_decode_eval_args(AvmCode * inCODE)
{
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( count == inCODE->size() )
			<< "Invalid statement ARGUMENTS initialization !!!\n"
			<< inCODE->toString( AVM_TAB1_INDENT )
			<< SEND_EXIT;

	argsInstruction = inCODE->getInstruction();
	if( (argsInstruction == NULL) || argsInstruction->isNops() ||
		(argsBytecode = argsInstruction->getBytecode())[0].isNopsOperation() )
	{
		values = &( inCODE->getArgs() );

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
	AVM_OS_TRACE << "args[nops]:>>" << AVM_STR_INDENT;
	argsStream(AVM_OS_TRACE);
	AVM_OS_TRACE << END_INDENT_EOL;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )

		return( true );
	}

	else switch( argsInstruction->getMainContext() )
	{
		case AVM_ARG_STANDARD_CTX:
		{
			return( decode_eval_args_processor(
					argsInstruction->getMainBytecode(), inCODE) );
		}

		case AVM_ARG_ARGUMENT_CTX:
		case AVM_ARG_PARAMETER_CTX:
		case AVM_ARG_RETURN_CTX:
		{
			return( decode_eval_args_processor(
					argsInstruction->getMainBytecode(), inCODE) );
		}

		case AVM_ARG_UNDEFINED_CONTEXT:
		default:
		{
			return( false );
		}
	}
}


bool ARGS_ENV::decode_eval_args_context(
		AvmBytecode & bytecode, AvmCode * inCODE)
{
//	AVM_OS_ASSERT_FATAL_ERROR_EXIT( count == inCODE->size() )
//			<< "Invalid statement ARGUMENTS initialization !!!\n"
//			<< inCODE->toString( AVM_TAB1_INDENT )
//			<< SEND_EXIT;
//
//	argsInstruction = inCODE->getInstruction();
//	if( (argsInstruction == NULL) || argsInstruction->isNops() ||
//		(argsBytecode = argsInstruction->getBytecode())[0].isNops() )
//	{
//		values = &( inCODE->getArgs() );
//
//		return( true );
//	}

	switch( bytecode.context )
	{
		case AVM_ARG_STANDARD_CTX:
		{
			return( decode_eval_args_processor(bytecode, inCODE) );
		}

		case AVM_ARG_ARGUMENT_CTX:
		case AVM_ARG_PARAMETER_CTX:
		case AVM_ARG_RETURN_CTX:
		{
			return( decode_eval_args_processor(bytecode, inCODE) );
		}

		case AVM_ARG_UNDEFINED_CONTEXT:
		default:
		{
			return( false );
		}
	}
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// 	 DECODE EVAL PROCESSOR
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool ARGS_ENV::decode_eval_args_processor(
		AvmBytecode & bytecode, AvmCode * inCODE)
{
	avm_size_t CURRENT_CALL_COUNT;

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
	CURRENT_CALL_COUNT = ++ARGS_ENV::CALL_COUNT;

	AVM_OS_TRACE << "args[" << CURRENT_CALL_COUNT << "]:<< ";
	inCODE->toDebug( AVM_OS_TRACE << AVM_SPC_INDENT ) << END_INDENT_EOL;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )

	argsBytecode = (argsInstruction = inCODE->getInstruction())->getBytecode();

	if( argsInstruction->isNops() || argsBytecode[0].isNopsOperation() )
	{
		values = &( inCODE->getArgs() );

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
	AVM_OS_TRACE << "args[nops:" << CURRENT_CALL_COUNT << ">]:>>";
	argsStream( AVM_OS_TRACE << AVM_STR_INDENT );
	AVM_OS_TRACE << END_INDENT_EOL;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )

		return( true );
	}

	AvmCode::iterator it = inCODE->begin();
	for( begin() ; hasNext() ; ++it , next() )
	{
		switch( argsBytecode[idx].processor )
		{
			case AVM_ARG_NOP_CPU:
			{
				current( *it );

				break;
			}
			case AVM_ARG_NOPS_CPU:
			{
				current_next( *it );
				for( ++it ; hasNext() ; ++it )
				{
					current_next( *it );
				}

				break;
			}

			case AVM_ARG_MEMORY_LVALUE_CPU:
			{
				if( eval_processor_dma_lvalue(argsBytecode[idx], *it) )
				{
					break;
				}
				else
				{
					return( false );
				}
			}

			case AVM_ARG_MEMORY_WVALUE_CPU:
			{
				if( eval_processor_dma_wvalue(argsBytecode[idx], *it) )
				{
					break;
				}
				else
				{
					return( false );
				}
			}

			case AVM_ARG_MEMORY_RVALUE_CPU:
			{
				if( eval_processor_dma_rvalue(argsBytecode[idx], *it) )
				{
					break;
				}
				else
				{
					return( false );
				}
			}

			case AVM_ARG_MEMORY_MACHINE_CPU:
			{
				if( eval_processor_dma_machine(argsBytecode[idx], *it) )
				{
					break;
				}
				else
				{
					return( false );
				}
			}

			case AVM_ARG_ARITHMETIC_LOGIC_CPU:
			{
				if( eval_processor_alu(argsBytecode[idx], *it) )
				{
					break;
				}
				else
				{
					return( false );
				}
			}


			case AVM_ARG_CHARACTER_CPU:
			{
				if( eval_processor_character(argsBytecode[idx], *it) )
				{
					break;
				}
				else
				{
					return( false );
				}
			}

			case AVM_ARG_STRING_CPU:
			{
				if( eval_processor_string(argsBytecode[idx], *it) )
				{
					break;
				}
				else
				{
					return( false );
				}
			}

			case AVM_ARG_ARRAY_LVALUE_CPU:
			{
				if( eval_processor_array_lvalue(argsBytecode[idx], *it) )
				{
					break;
				}
				else
				{
					return( false );
				}
			}
			case AVM_ARG_ARRAY_RVALUE_CPU:
			{
				if( eval_processor_array_rvalue(argsBytecode[idx], *it) )
				{
					break;
				}
				else
				{
					return( false );
				}
			}

			case AVM_ARG_VECTOR_CPU:
			{
				if( eval_processor_vector(argsBytecode[idx], *it) )
				{
					break;
				}
				else
				{
					return( false );
				}
			}

			case AVM_ARG_QUEUE_CPU:
			case AVM_ARG_LIST_CPU:
			case AVM_ARG_COLLECTION_CPU:
			{
				if( eval_processor_collection(argsBytecode[idx], *it) )
				{
					break;
				}
				else
				{
					return( false );
				}
			}

			case AVM_ARG_BUFFER_CPU:
			{
				if( eval_processor_buffer(argsBytecode[idx], *it) )
				{
					break;
				}
				else
				{
					return( false );
				}
			}

			case AVM_ARG_STATEMENT_CPU:
			{
				if( eval_processor_statement(
						argsBytecode[idx], (*it).to_ptr< AvmCode >()) )
				{
					break;
				}
				else
				{
					return( false );
				}
			}

			case AVM_ARG_UNDEFINED_PROCESSOR:
			default:
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "ARGS_ENV::decode_eval_processor :> "
							"Unexpected bytecode<processor> << "
						<< argsBytecode[idx].strCode()
						<< " >> for : " << (*it).str() << " !!!"
						<< SEND_EXIT;

				break;
			}
		}
	}

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
	AVM_OS_TRACE << "args[" << CURRENT_CALL_COUNT << "]:>>" << AVM_STR_INDENT;
	argsStream(AVM_OS_TRACE);
	AVM_OS_TRACE << END_INDENT_EOL;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )

	return( true );
}


bool ARGS_ENV::decode_eval_processor(
		AvmBytecode & bytecode, AvmCode * inCODE)
{
	switch( bytecode.processor )
	{
//		case AVM_ARG_NO_OPERATION_CPU:
//		{
//			current( inCODE );
//
//			return( true );
//		}
//
//		case AVM_ARG_MEMORY_LVALUE_CPU:
//		{
//			return( eval_processor_dma_lvalue(bytecode, inCODE) );
//		}
//
//		case AVM_ARG_MEMORY_WVALUE_CPU:
//		{
//			return( eval_processor_dma_wvalue(bytecode, inCODE) );
//		}

		case AVM_ARG_MEMORY_RVALUE_CPU:
		{
			return( eval_processor_dma_rvalue(bytecode, inCODE) );
		}

		case AVM_ARG_MEMORY_MACHINE_CPU:
		{
			return( eval_processor_dma_machine(bytecode, inCODE) );
		}

		case AVM_ARG_ARITHMETIC_LOGIC_CPU:
		{
			return( eval_processor_alu(bytecode, inCODE) );
		}


		case AVM_ARG_CHARACTER_CPU:
		{
			return( eval_processor_character(bytecode, inCODE) );
		}

		case AVM_ARG_STRING_CPU:
		{
			return( eval_processor_string(bytecode, inCODE) );
		}

//		case AVM_ARG_ARRAY_LVALUE_CPU:
//		{
//			return( eval_processor_array_lvalue(bytecode, inCODE) );
//		}
//		case AVM_ARG_ARRAY_RVALUE_CPU:
//		{
//			return( eval_processor_array_rvalue(bytecode, inCODE) );
//		}

		case AVM_ARG_VECTOR_CPU:
		{
			return( eval_processor_vector(bytecode, inCODE) );
		}

		case AVM_ARG_QUEUE_CPU:
		case AVM_ARG_LIST_CPU:
		case AVM_ARG_COLLECTION_CPU:
		{
			return( eval_processor_collection(bytecode, inCODE) );
		}

		case AVM_ARG_BUFFER_CPU:
		{
			return( eval_processor_buffer(bytecode, inCODE) );
		}

		case AVM_ARG_STATEMENT_CPU:
		{
			return( eval_processor_statement(bytecode, inCODE) );
		}

		case AVM_ARG_UNDEFINED_PROCESSOR:
		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "ARGS_ENV::decode_eval_processor :> "
						"Unexpected bytecode<processor> << "
					<< bytecode.strCode() << " >> for : "
					<< inCODE->strDebug() << " !!!"
					<< SEND_EXIT;

			return( false );
		}
	}
}


bool ARGS_ENV::decode_eval_processor(AvmBytecode & bytecode, BF & arg)
{
	switch( bytecode.processor )
	{
		case AVM_ARG_NOP_CPU:
		case AVM_ARG_NOPS_CPU:
		{
			current( arg );

			return( true );
		}

		case AVM_ARG_MEMORY_LVALUE_CPU:
		{
			return( eval_processor_dma_lvalue(bytecode, arg) );
		}

		case AVM_ARG_MEMORY_WVALUE_CPU:
		{
			return( eval_processor_dma_wvalue(bytecode, arg) );
		}

		case AVM_ARG_MEMORY_RVALUE_CPU:
		{
			return( eval_processor_dma_rvalue(bytecode, arg) );
		}

		case AVM_ARG_MEMORY_MACHINE_CPU:
		{
			return( eval_processor_dma_machine(bytecode, arg) );
		}

		case AVM_ARG_ARITHMETIC_LOGIC_CPU:
		{
			return( eval_processor_alu(bytecode, arg) );
		}


		case AVM_ARG_CHARACTER_CPU:
		{
			return( eval_processor_character(bytecode, arg) );
		}

		case AVM_ARG_STRING_CPU:
		{
			return( eval_processor_string(bytecode, arg) );
		}

		case AVM_ARG_ARRAY_LVALUE_CPU:
		{
			return( eval_processor_array_lvalue(bytecode, arg) );
		}
		case AVM_ARG_ARRAY_RVALUE_CPU:
		{
			return( eval_processor_array_rvalue(bytecode, arg) );
		}

		case AVM_ARG_VECTOR_CPU:
		{
			return( eval_processor_vector(bytecode, arg) );
		}

		case AVM_ARG_QUEUE_CPU:
		case AVM_ARG_LIST_CPU:
		case AVM_ARG_COLLECTION_CPU:
		{
			return( eval_processor_collection(bytecode, arg) );
		}

		case AVM_ARG_BUFFER_CPU:
		{
			return( eval_processor_buffer(bytecode, arg) );
		}

		case AVM_ARG_STATEMENT_CPU:
		{
			return( eval_processor_statement(
					bytecode, (arg).to_ptr< AvmCode >()) );
		}

		case AVM_ARG_UNDEFINED_PROCESSOR:
		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "ARGS_ENV::decode_eval_processor :> "
						"Unexpected bytecode<processor> << "
					<< bytecode.strCode() << " >> for : "
					<< arg.str() << " !!!"
					<< SEND_EXIT;

			return( false );
		}
	}
}


BF ARGS_ENV::return_decode_eval_processor(AvmBytecode & bytecode, BF & arg)
{
	InstructionEnvironment EVAL_ARG(ENV, outED, 1);
	if( EVAL_ARG.mARG->decode_eval_processor(bytecode, arg) )
	{
		return( EVAL_ARG.mARG->at(0) );
	}
	else
	{
		return( arg );
	}
}

bool ARGS_ENV::decode_eval_processor(BFCode & aCode)
{
	if( not aCode->hasInstruction() )
	{
		if( not ENV->getBuilder().getAvmcodeCompiler().optimizeEvalExpression(
				ENV->inED->getParametersRID().getExecutable(), aCode) )
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "ARGS_ENV::decode_eval_processor :> "
						"Unexpected a code without instruction << "
					<< aCode->str() << " >> !!!"
					<< SEND_EXIT;
		}
	}

	return( decode_eval_processor(
			aCode->getInstruction()->getMainBytecode(), aCode) );
}

BF ARGS_ENV::return_decode_eval_processor(BFCode & aCode)
{
	InstructionEnvironment EVAL_ARG(ENV, outED, 1);
	if( EVAL_ARG.mARG->decode_eval_processor(aCode) )
	{
		return( EVAL_ARG.mARG->at(0) );
	}
	else
	{
		return( BF::REF_NULL );
	}
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// EVAL PROCESSOR MEMORY UFI POINTER
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/**
 * EVAL PROCESSOR < AVM_ARG_MEMORY_UFI_POINTER_CPU >
 */
bool ARGS_ENV::eval_processor_dma_lvalue_ufi_pointer(
		AvmBytecode & bytecode, BF & arg)
{
	InstanceOfData * lvalue = arg.to_ptr< InstanceOfData >();

	avm_size_t * aRelativeOffsetPath =
			new avm_size_t[ lvalue->getDataPath()->size() + 1 ];

	InstanceOfData * aRoot = lvalue;
	if( lvalue->getModifier().hasNatureReference() )
	{
		aRoot = ENV->getRvalue(outED, lvalue->getAliasTarget()->to<
				InstanceOfData >()).as_ptr< InstanceOfData >();
	}

	aRelativeOffsetPath[0] = aRoot->getOffset();

	InstanceOfData * ptrValue =
			new InstanceOfData(lvalue, aRoot, aRelativeOffsetPath);

	current( BF( ptrValue ) );

	// For Array Value Size
	BF rvalue;

	if( ptrValue->hasRuntimeContainerRID() )
	{
		rvalue = outED->getRuntime( ptrValue->getRuntimeContainerRID() ).
				getData( ptrValue->getOffset() );
	}
	else
	{
		RuntimeID aDataRID;

		if( ENV->getRuntimeForm(outED, outED->mRID, ptrValue, aDataRID) )
		{
			ptrValue->setRuntimeContainerRID( aDataRID );

			rvalue = outED->getRuntime(aDataRID).getData( ptrValue->getOffset() );
		}
		else
		{
			LocalRuntime aLocalRuntime;
			if( ENV->getRuntimeForm(outED, lvalue, aLocalRuntime) )
			{
				rvalue = aLocalRuntime.getDataTable().at( ptrValue->getOffset() );
			}
			else
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "ARGS_ENV::eval_processor_dma_lvalue_ufi_pointer:> "
							"Failed to found data table for the "
							"instance of data :>\n"
						<< ptrValue->toString( AVM_TAB1_INDENT )
						<< SEND_EXIT;

				current( arg );

				return( false );
			}
		}
	}

	TableOfSymbol::iterator itPath = lvalue->getDataPath()->begin();
	TableOfSymbol::iterator endPath = lvalue->getDataPath()->end();
	for( avm_size_t k = 1 ; itPath != endPath ; ++k, ++itPath )
	{
		switch( (*itPath).getPointerNature() )
		{
			case IPointerDataNature::POINTER_FIELD_CLASS_ATTRIBUTE_NATURE:
			case IPointerDataNature::POINTER_FIELD_ARRAY_OFFSET_NATURE:
			{
				aRelativeOffsetPath[k] = (*itPath).getOffset();

				break;
			}
			case IPointerDataNature::POINTER_FIELD_ARRAY_INDEX_NATURE:
			{
				BF bfOffset = return_decode_eval_rvalue( (*itPath).getValue() );
				if( bfOffset.invalid() )
				{
					AVM_OS_FATAL_ERROR_EXIT
							<<  "Failed to eval ARRAY index << "
							<< (*itPath).strValue()
							<< " >> in variable << " << (*itPath).str()
							<< " >> for writing in VVT !!!"
							<< SEND_EXIT;

					return( false );
				}

				if( bfOffset.isNumeric() )
				{
					AVM_OS_ASSERT_FATAL_ARRAY_OFFSET_EXIT( bfOffset.toInteger(),
						static_cast< avm_integer_t >(rvalue.size()) )
							<< "Failed to write in ARRAY with index << "
							<< bfOffset.toInteger() << " >> in variable << "
							<< lvalue->str() << " >> for writing in VVT !!!"
							<< SEND_EXIT;

					aRelativeOffsetPath[k] = bfOffset.toInteger();

					break;
				}

				else
				{
					avm_size_t offset = ENV->genNumericOffset(
							outED, outED->mRID, (*itPath),
							bfOffset, 0, (rvalue.size() - 1) );

					if( offset != AVM_NUMERIC_MAX_SIZE_T )
					{
						aRelativeOffsetPath[k] = offset;

						break;
					}
				}

				outED.mwsetAEES( AEES_SYMBOLIC_EXECUTION_LIMITATION );

				AVM_OS_FATAL_ERROR_EXIT
						<< "BaseEnvironment::setData:> "
							"unexpected NON-INTEGER ARRAY INDEX << "
						<< bfOffset.str() << " >> in instance FQN-ID :>\n"
						<< lvalue->toString( AVM_TAB1_INDENT )
						<< SEND_EXIT;

				return( false );
			}
			default:
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "ARGS_ENV::eval_processor_dma_lvalue_ufi_pointer:> "
						"Unexpected POINTER NATURE for the instance of data :>\n"
						<< lvalue->toString( AVM_TAB1_INDENT )
						<< SEND_EXIT;

				return( false );
			}
		}

		rvalue.moveAt( aRelativeOffsetPath[k] );

		if( (*itPath).getModifier().hasNatureReference() )
		{
			rvalue = ENV->getRvalue(outED, rvalue.as_ptr< InstanceOfData >() );
		}
	}

	return( true );
}


bool ARGS_ENV::eval_processor_dma_wvalue_ufi_pointer(
		AvmBytecode & bytecode, BF & arg)
{
	InstanceOfData * lvalue = arg.to_ptr< InstanceOfData >();

	TableOfSymbol::iterator itPath = lvalue->getDataPath()->begin();
	TableOfSymbol::iterator endPath = lvalue->getDataPath()->end();

	if( lvalue->getModifier().hasNatureReference() )
	{
		lvalue = ENV->getRvalue(outED, lvalue->getAliasTarget()->to<
				InstanceOfData >()).as_ptr< InstanceOfData >();
	}

	// For Array Value Size
	BF rvalue;

	if( lvalue->hasRuntimeContainerRID() )
	{
		rvalue = outED.getWritableRuntime(
				lvalue->getRuntimeContainerRID() ).
						getWritableData( lvalue->getOffset() );
	}
	else
	{
		RuntimeID aDataRID;

		if( ENV->getRuntimeForm(outED, outED->mRID, lvalue, aDataRID) )
		{
			rvalue = outED.getWritableRuntimeDataTable(aDataRID)->
					getWritable( lvalue->getOffset() );
		}
		else
		{
			LocalRuntime aLocalRuntime;
			if( ENV->getRuntimeForm(outED, lvalue, aLocalRuntime) )
			{
				outED.makeModifiableLocalRuntime( aLocalRuntime );

				rvalue = aLocalRuntime.getDataTable().
						getWritable( lvalue->getOffset() );
			}
			else
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "ARGS_ENV::eval_processor_dma_rvalue_ufi_pointer:> "
							"Failed to found data table for the "
							"instance of data :>\n"
						<< lvalue->toString( AVM_TAB1_INDENT )
						<< SEND_EXIT;

				current( arg );

				return( false );
			}
		}
	}

	for( avm_size_t offset = 0; itPath != endPath ; ++itPath )
	{
		switch( (*itPath).getPointerNature() )
		{
			case IPointerDataNature::POINTER_FIELD_CLASS_ATTRIBUTE_NATURE:
			case IPointerDataNature::POINTER_FIELD_ARRAY_OFFSET_NATURE:
			{
				offset = (*itPath).getOffset();

				break;
			}
			case IPointerDataNature::POINTER_FIELD_ARRAY_INDEX_NATURE:
			{
				BF bfOffset = return_decode_eval_rvalue( (*itPath).getValue() );
				if( bfOffset.invalid() )
				{
					AVM_OS_FATAL_ERROR_EXIT
							<<  "Failed to eval ARRAY index << "
							<< (*itPath).strValue()
							<< " >> in variable << " << (*itPath).str()
							<< " >> for writing in VVT !!!"
							<< SEND_EXIT;

					return( false );
				}

				if( bfOffset.isNumeric() )
				{
					AVM_OS_ASSERT_FATAL_ARRAY_OFFSET_EXIT( bfOffset.toInteger(),
						static_cast< avm_integer_t >(rvalue.size()) )
							<< "Failed to write in ARRAY with index << "
							<< bfOffset.toInteger() << " >> in variable << "
							<< lvalue->str() << " >> for writing in VVT !!!"
							<< SEND_EXIT;

					offset = bfOffset.toInteger();

					break;
				}

				else
				{
					offset = ENV->genNumericOffset( outED, outED->mRID,
							(*itPath), bfOffset, 0, (rvalue.size() - 1) );

					if( offset != AVM_NUMERIC_MAX_SIZE_T )
					{
						break;
					}
				}

				outED.mwsetAEES( AEES_SYMBOLIC_EXECUTION_LIMITATION );

				AVM_OS_FATAL_ERROR_EXIT
						<< "BaseEnvironment::setData:> "
							"unexpected NON-INTEGER ARRAY INDEX << "
						<< bfOffset.str() << " >> in instance FQN-ID :>\n"
						<< lvalue->toString( AVM_TAB1_INDENT )
						<< SEND_EXIT;

				return( false );
			}
			default:
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "ARGS_ENV::eval_processor_dma_wvalue_ufi_pointer:> "
						"Unexpected POINTER NATURE for the instance of data :>\n"
						<< lvalue->toString( AVM_TAB1_INDENT )
						<< SEND_EXIT;

				return( false );
			}
		}

		rvalue.moveAtWritable( offset );

		if( (*itPath).getModifier().hasNatureReference() )
		{
			rvalue = ENV->getWvalue(outED, rvalue.as_ptr< InstanceOfData >() );
		}
	}

	current( rvalue );

	return( true );
}


bool ARGS_ENV::eval_processor_dma_rvalue_ufi_pointer(
		AvmBytecode & bytecode, BF & arg)
{
	InstanceOfData * lvalue = arg.to_ptr< InstanceOfData >();

	TableOfSymbol::iterator itPath = lvalue->getDataPath()->begin();
	TableOfSymbol::iterator endPath = lvalue->getDataPath()->end();

	if( lvalue->getModifier().hasNatureReference() )
	{
		lvalue = ENV->getRvalue(outED, lvalue->getAliasTarget()->to<
				InstanceOfData >()).as_ptr< InstanceOfData >();
	}

	// For Array Value Size
	BF rvalue;

	if( lvalue->hasRuntimeContainerRID() )
	{
		rvalue = outED->getRuntime( lvalue->getRuntimeContainerRID() ).
						getData( lvalue->getOffset() );
	}
	else
	{
		RuntimeID aDataRID;

		if( ENV->getRuntimeForm(outED, outED->mRID, lvalue, aDataRID) )
		{
			rvalue = outED->getRuntime(aDataRID).getData( lvalue->getOffset() );
		}
		else
		{
			LocalRuntime aLocalRuntime;
			if( ENV->getRuntimeForm(outED, lvalue, aLocalRuntime) )
			{
				rvalue = aLocalRuntime.getDataTable().at( lvalue->getOffset() );
			}
			else
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "ARGS_ENV::eval_processor_dma_rvalue_ufi_pointer:> "
							"Failed to found data table for the "
							"instance of data :>\n"
						<< lvalue->toString( AVM_TAB1_INDENT )
						<< SEND_EXIT;

				current( arg );

				return( false );
			}
		}
	}

	for( avm_size_t offset = 0; itPath != endPath ; ++itPath )
	{
		switch( (*itPath).getPointerNature() )
		{
			case IPointerDataNature::POINTER_FIELD_CLASS_ATTRIBUTE_NATURE:
			case IPointerDataNature::POINTER_FIELD_ARRAY_OFFSET_NATURE:
			{
				offset = (*itPath).getOffset();

				break;
			}
			case IPointerDataNature::POINTER_FIELD_ARRAY_INDEX_NATURE:
			{
				BF bfOffset = return_decode_eval_rvalue( (*itPath).getValue() );
				if( bfOffset.invalid() )
				{
					AVM_OS_FATAL_ERROR_EXIT
							<<  "Failed to eval ARRAY index << "
							<< (*itPath).strValue()
							<< " >> in variable << " << (*itPath).str()
							<< " >> for writing in VVT !!!"
							<< SEND_EXIT;

					return( false );
				}

				if( bfOffset.isNumeric() )
				{
					AVM_OS_ASSERT_FATAL_ARRAY_OFFSET_EXIT( bfOffset.toInteger(),
						static_cast< avm_integer_t >(rvalue.size()) )
							<< "Failed to write in ARRAY with index << "
							<< bfOffset.toInteger() << " >> in variable << "
							<< lvalue->str() << " >> for writing in VVT !!!"
							<< SEND_EXIT;

					offset = bfOffset.toInteger();

					break;
				}

				else
				{
					offset = ENV->genNumericOffset(outED, outED->mRID,
							(*itPath), bfOffset, 0, (rvalue.size() - 1) );

					if( offset != AVM_NUMERIC_MAX_SIZE_T )
					{
						break;
					}
				}

				outED.mwsetAEES( AEES_SYMBOLIC_EXECUTION_LIMITATION );

				AVM_OS_FATAL_ERROR_EXIT
						<< "BaseEnvironment::setData:> "
							"unexpected NON-INTEGER ARRAY INDEX << "
						<< bfOffset.str() << " >> in instance FQN-ID :>\n"
						<< lvalue->toString( AVM_TAB1_INDENT )
						<< SEND_EXIT;

				return( false );
			}
			default:
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "ARGS_ENV::eval_processor_dma_rvalue_ufi_pointer:> "
						"Unexpected POINTER NATURE for the instance of data :>\n"
						<< lvalue->toString( AVM_TAB1_INDENT )
						<< SEND_EXIT;

				return( false );
			}
		}

		rvalue.moveAt( offset );

		if( (*itPath).getModifier().hasNatureReference() )
		{
			rvalue = ENV->getRvalue(outED, rvalue.as_ptr< InstanceOfData >() );
		}
	}

	current( rvalue );

	return( true );
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// EVAL PROCESSOR MEMORY LVALUE
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/**
 * EVAL PROCESSOR < AVM_ARG_MEMORY_LVALUE_CPU >
 */
bool ARGS_ENV::eval_processor_dma_lvalue(AvmBytecode & bytecode, BF & arg)
{
	switch( bytecode.operand )
	{
		case AVM_ARG_DATA_KIND:
		{
			current( arg );

			return( true );
		}

		case AVM_ARG_DATA_REF_KIND:
		{
			current( ENV->getRvalue(outED, arg.to_ptr< InstanceOfData >()) );

			return( true );
		}

		case AVM_ARG_DATA_MACRO_KIND:
		{
			const BF & lvalue =
					ENV->getRvalue(outED, arg.to_ptr< InstanceOfData >());

			if( lvalue.is< InstanceOfData >() )
			{
				current( lvalue );

				return( true );
			}
			else
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "Unexpected to eval_processor_dma_lvalue << "
						<< lvalue.str() << " >> for : " << arg.str() << " !!!"
						<< SEND_EXIT;

				return( false );
			}
		}

		case AVM_ARG_DATA_UFI_KIND:
		{
			return( eval_processor_dma_lvalue_ufi_pointer(bytecode, arg) );
		}

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "ARGS_ENV::eval_processor_dma_lvalue :> "
						"Unexpected argcode << " << bytecode.strCode()
					<< " >> for : " << arg.str() << " !!!"
					<< SEND_EXIT;

			current( arg );

			return( false );
		}
	}
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// EVAL PROCESSOR MEMORY WVALUE
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/**
 * EVAL PROCESSOR < AVM_ARG_MEMORY_WVALUE_CPU >
 */
bool ARGS_ENV::eval_processor_dma_wvalue(AvmBytecode & bytecode, BF & arg)
{
	switch( bytecode.operand )
	{
		case AVM_ARG_DATA_KIND:
		{
			current( ENV->getWvalue(outED, arg.to_ptr< InstanceOfData >()) );

			return( true );
		}

		case AVM_ARG_DATA_REF_KIND:
		{
			current( ENV->getWvalue(outED,
					ENV->getRvalue(outED, arg.to_ptr< InstanceOfData >()).
					as_ptr< InstanceOfData >() ));

			return( true );
		}

		case AVM_ARG_DATA_MACRO_KIND:
		{
			const BF & lvalue = ENV->getRvalue(outED,
					arg.to_ptr< InstanceOfData >());

			if( lvalue.is< InstanceOfData >() )
			{
				current( ENV->getWvalue(outED,
						lvalue.to_ptr< InstanceOfData >() ));

				return( true );
			}
			else
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "Unexpected to eval_processor_dma_wvalue << "
						<< lvalue.str() << " >> for : " << arg.str() << " !!!"
						<< SEND_EXIT;

				return( false );
			}
		}

		case AVM_ARG_DATA_UFI_KIND:
		{
			return( eval_processor_dma_wvalue_ufi_pointer(bytecode, arg) );
		}


		case AVM_ARG_BUFFER_KIND:
		{
			const RuntimeID & aRID = outED->getRuntimeContainerRID(
					arg.to_ptr< InstanceOfBuffer >());

			AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( aRID )
					<< "RID container for the buffer< "
					<< arg.to_ptr< InstanceOfBuffer >()->str() << " > !!!"
					<< SEND_EXIT;

			current( outED.getWritableRuntime( aRID ).bfWritableBuffer(
					arg.to_ptr< InstanceOfBuffer >() ) );

			return( true );
		}

		case AVM_ARG_BUILTIN_CONTAINER_KIND:
		{
			arg.makeWritable();

			current( arg );

			return( true );
		}

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "ARGS_ENV::eval_processor_dma_wvalue :> "
						"Unexpected argcode << " << bytecode.strCode()
					<< " >> for : " << arg.str() << " !!!"
					<< SEND_EXIT;

			current( arg );

			return( false );
		}
	}
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// EVAL PROCESSOR MEMORY RVALUE
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/**
 * EVAL PROCESSOR < AVM_ARG_MEMORY_RVALUE_CPU >
 */
bool ARGS_ENV::eval_processor_dma_rvalue(AvmBytecode & bytecode, BF & arg)
{
	switch( bytecode.operand )
	{
		case AVM_ARG_DATA_KIND:
		{
			current( ENV->getRvalue(outED, arg.to_ptr< InstanceOfData >()) );

			return( true );
		}

		case AVM_ARG_DATA_CST_KIND:
		{
			current( arg );

			return( true );
		}

		case AVM_ARG_DATA_REF_KIND:
		{
			current( ENV->getRvalue(outED,
					ENV->getRvalue(outED, arg.to_ptr< InstanceOfData >()).
					as_ptr< InstanceOfData >()) );

			return( true );
		}

		case AVM_ARG_DATA_MACRO_KIND:
		{
			BF & rvalue  = ENV->getRvalue(outED,
					arg.to_ptr< InstanceOfData >());

			if( rvalue.is< InstanceOfData >() )
			{
				current( ENV->getRvalue(outED,
						rvalue.to_ptr< InstanceOfData >() ));

				return( true );
			}
			else
			{
				return( decode_eval_rvalue( rvalue ) );
			}
		}

		case AVM_ARG_DATA_UFI_KIND:
		{
			return( eval_processor_dma_rvalue_ufi_pointer(bytecode, arg) );
		}

		case AVM_ARG_EXPRESSION_KIND:
		{
			return( eval_processor_dma_rvalue(
					bytecode, arg.to_ptr< AvmCode >()) );
		}

		case AVM_ARG_BUILTIN_CONTAINER_KIND:
		{
			current( arg );

			return( true );
		}

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "ARGS_ENV::eval_processor_dma_rvalue :> "
						"Unexpected argcode << " << bytecode.strCode()
					<< " >> for : " << arg.str() << " !!!"
					<< SEND_EXIT;

			current( arg );

			return( false );
		}
	}
}


bool ARGS_ENV::eval_processor_dma_rvalue(AvmBytecode & bytecode, AvmCode * aCode)
{
	InstructionEnvironment EVAL_ARG(ENV, outED, aCode->size());
	if( EVAL_ARG.mARG->decode_eval_args_processor(bytecode, aCode) )
	{
		outED = EVAL_ARG.mARG->outED;
	}
	else
	{
		return( false );
	}

	switch( aCode->getAvmOpCode() )
	{
		case AVM_OPCODE_ASSIGN:
		{
			current( EVAL_ARG.mARG->at(1) );

AVM_IF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )
AVM_OS_TRACE << "dma:lvalue:> "
		<< str_header( EVAL_ARG.mARG->at(0).to_ptr< InstanceOfData >() )
		<< std::endl
		<< "dma:rvalue:> " << EVAL_ARG.mARG->at(1).str()
		<< std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )

			return( ENV->setRvalue( outED,
					EVAL_ARG.mARG->at(0).to_ptr< InstanceOfData >(),
					EVAL_ARG.mARG->at(1) ));
		}

		case AVM_OPCODE_ASSIGN_AFTER:
		{
			current( ENV->getRvalue( outED,
					EVAL_ARG.mARG->at(0).to_ptr< InstanceOfData >() ));

AVM_IF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )
AVM_OS_TRACE << "dma:lvalue:> "
		<< str_header( EVAL_ARG.mARG->at(0).to_ptr< InstanceOfData >() )
		<< std::endl
		<< "dma:rvalue:> " << EVAL_ARG.mARG->at(1).str()
		<< std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )

			current( EVAL_ARG.mARG->at(1) );

			return( ENV->setRvalue( outED,
					EVAL_ARG.mARG->at(0).to_ptr< InstanceOfData >(),
					EVAL_ARG.mARG->at(2) ));
		}


		case AVM_OPCODE_ASSIGN_NEWFRESH:
		{
			BFList paramList;
			BF aNewSymbolicConstant = ENV->createNewFreshParam(outED->mRID,
					EVAL_ARG.mARG->at(0).to_ptr< InstanceOfData >(), paramList );

			current( aNewSymbolicConstant );

AVM_IF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )
AVM_OS_TRACE << "dma:lvalue:> "
		<< str_header( EVAL_ARG.mARG->at(0).to_ptr< InstanceOfData >() )
		<< std::endl
		<< "dma:rvalue:> " << aNewSymbolicConstant.str()
		<< std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )

			if( ENV->setRvalue(outED, EVAL_ARG.mARG->at(0).
					to_ptr< InstanceOfData >(), aNewSymbolicConstant) )
			{
				ExecutionDataFactory::appendIOElementTrace(outED,
					BF(new ExecutionConfiguration(outED->mRID,
						StatementConstructor::newCode(
							OperatorManager::OPERATOR_ASSIGN_NEWFRESH,
							EVAL_ARG.mARG->at(0), aNewSymbolicConstant))));

				outED.appendParameters( paramList );

				return( true );
			}
			else
			{
				return( false );
			}
		}

//		case AVM_OPCODE_ASSIGN_RESET:

		case AVM_OPCODE_CTOR:
		{
			current( EVAL_ARG.mARG->at(0) );

			return( true );
		}

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "ARGS_ENV::eval_processor_dma_rvalue :> "
					"Unexpected opcode << " << aCode->strDebug() << " >> !!!"
					<< SEND_EXIT;

			return( false );
		}
	}
}


bool ARGS_ENV::decode_eval_rvalue(BF & arg)
{
	switch( arg.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			return( decode_eval_processor( arg.to_ptr< AvmCode >()
					->getInstruction()->getMainBytecode(),
					arg.to_ptr< AvmCode >()) );
		}

		case FORM_INSTANCE_DATA_KIND:
		{
			InstanceOfData * anInstance = arg.to_ptr< InstanceOfData >();

			if( anInstance->getModifier().hasNatureReference() )
			{
				current( ENV->getRvalue(outED, ENV->getRvalue(outED,
						anInstance).to_ptr< InstanceOfData >() ));
			}
			else if( anInstance->getModifier().hasNatureMacro() )
			{
				return( decode_eval_rvalue( ENV->getRvalue(outED, anInstance) ));
			}
			else if( anInstance->getModifier().hasFeatureMutable() )
			{
				current( ENV->getRvalue(outED, anInstance) );
			}
			else
			{
				current( arg );
			}

			return( true );
		}

		case FORM_BUILTIN_BOOLEAN_KIND:
		case FORM_BUILTIN_INTEGER_KIND:
		case FORM_BUILTIN_RATIONAL_KIND:
		case FORM_BUILTIN_FLOAT_KIND:

		case FORM_BUILTIN_CHARACTER_KIND:
		case FORM_BUILTIN_STRING_KIND:
		case FORM_BUILTIN_IDENTIFIER_KIND:
		case FORM_BUILTIN_QUALIFIED_IDENTIFIER_KIND:

		case FORM_ARRAY_BOOLEAN_KIND:
		case FORM_ARRAY_CHARACTER_KIND:
		case FORM_ARRAY_INTEGER_KIND:
		case FORM_ARRAY_RATIONAL_KIND:
		case FORM_ARRAY_FLOAT_KIND:
		case FORM_ARRAY_STRING_KIND:
		case FORM_ARRAY_IDENTIFIER_KIND:
		case FORM_ARRAY_QUALIFIED_IDENTIFIER_KIND:

		case FORM_RUNTIME_ID_KIND:

		case FORM_INSTANCE_PORT_KIND:
		case FORM_INSTANCE_BUFFER_KIND:
		case FORM_INSTANCE_CONNECTOR_KIND:

		case FORM_OPERATOR_KIND:
		case FORM_AVMLAMBDA_KIND:
		case FORM_AVMPROGRAM_KIND:
		case FORM_AVMTRANSITION_KIND:
		case FORM_EXECUTABLE_MACHINE_KIND:
		case FORM_EXECUTABLE_SYSTEM_KIND:
		{
			current( arg );

			return( true );
		}

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "Failed to decode_eval_rvalue << "
					<< arg.str() << " >> as Value argument !!!"
					<< SEND_EXIT;

			return( false );
		}
	}
}


BF ARGS_ENV::return_decode_eval_rvalue(BF & arg)
{
	switch( arg.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			return( return_decode_eval_processor(arg.bfCode()) );
		}

		case FORM_INSTANCE_DATA_KIND:
		{
			InstanceOfData * anInstance = arg.to_ptr< InstanceOfData >();

			if( anInstance->getModifier().hasNatureReference() )
			{
				return( ENV->getRvalue(outED, ENV->getRvalue(outED,
						anInstance).to_ptr< InstanceOfData >() ));
			}
			else if( anInstance->getModifier().hasNatureMacro() )
			{
				return( return_decode_eval_rvalue(
						ENV->getRvalue(outED, anInstance) ));
			}
			else if( anInstance->getModifier().hasFeatureMutable() )
			{
				return( ENV->getRvalue(outED, anInstance) );
			}
			else
			{
				return( arg );
			}
		}

		case FORM_BUILTIN_BOOLEAN_KIND:
		case FORM_BUILTIN_INTEGER_KIND:
		case FORM_BUILTIN_RATIONAL_KIND:
		case FORM_BUILTIN_FLOAT_KIND:

		case FORM_BUILTIN_CHARACTER_KIND:
		case FORM_BUILTIN_STRING_KIND:
		case FORM_BUILTIN_IDENTIFIER_KIND:
		case FORM_BUILTIN_QUALIFIED_IDENTIFIER_KIND:

		case FORM_ARRAY_BOOLEAN_KIND:
		case FORM_ARRAY_CHARACTER_KIND:
		case FORM_ARRAY_INTEGER_KIND:
		case FORM_ARRAY_RATIONAL_KIND:
		case FORM_ARRAY_FLOAT_KIND:
		case FORM_ARRAY_STRING_KIND:
		case FORM_ARRAY_IDENTIFIER_KIND:
		case FORM_ARRAY_QUALIFIED_IDENTIFIER_KIND:

		case FORM_RUNTIME_ID_KIND:

		case FORM_INSTANCE_PORT_KIND:
		case FORM_INSTANCE_BUFFER_KIND:
		case FORM_INSTANCE_CONNECTOR_KIND:

		case FORM_OPERATOR_KIND:
		case FORM_AVMLAMBDA_KIND:
		case FORM_AVMPROGRAM_KIND:
		case FORM_AVMTRANSITION_KIND:
		case FORM_EXECUTABLE_MACHINE_KIND:
		case FORM_EXECUTABLE_SYSTEM_KIND:
		{
			return( arg );
		}

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "Failed to return_decode_eval_rvalue << "
					<< arg.str() << " >> as Value argument !!!"
					<< SEND_EXIT;

			return( BF::REF_NULL );
		}
	}
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// EVAL PROCESSOR MEMORY MACHINE as RID
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/**
 * EVAL PROCESSOR < AVM_ARG_MEMORY_MACHINE_CPU >
 */
bool ARGS_ENV::eval_processor_dma_machine(AvmBytecode & bytecode, BF & arg)
{
	switch( bytecode.operand )
	{
		case AVM_ARG_SELF_RID:
		{
			current( outED->mRID );

			return( true );
		}
		case AVM_ARG_PARENT_RID:
		{
			current( outED->mRID.getPRID() );

			return( true );
		}
		case AVM_ARG_COMMUNICATOR_RID:
		{
			current( outED->mRID.getCommunicator() );

			return( true );
		}
		case AVM_ARG_SYSTEM_RID:
		{
			current( outED->getSystemRID() );

			return( true );
		}

		case AVM_ARG_ENVIRONMENT_RID:
		{
			current( RuntimeLib::RID_ENVIRONMENT );

			return( true );
		}

		case AVM_ARG_COMPONENT_SELF_RID:
		{
			current( outED->mRID.getComponentSelf() );

			return( true );
		}
		case AVM_ARG_COMPONENT_PARENT_RID:
		{
			current( outED->mRID.getComponentParent() );

			return( true );
		}
		case AVM_ARG_COMPONENT_COMMUNICATOR_RID:
		{
			current( outED->mRID.getComponentCommunicator() );

			return( true );
		}

		case AVM_ARG_MACHINE_RID:
		{
			InstanceOfMachine * aMachine = arg.to_ptr< InstanceOfMachine >();

			if( aMachine->getExecutable()->hasSingleRuntimeInstance() )
			{
				bytecode.setNopCpu();
				if( (count == 1) && (idx == 0) )
				{
					bytecode.setNopsOperation();
				}

				current( arg = outED->getRuntimeID( aMachine ) );
			}
			else
			{
				current( outED->getRuntimeID( aMachine ) );
			}

			return( true );
		}

		case AVM_ARG_DATA_KIND:
		{
			current( ENV->getRvalue(outED, arg.to_ptr< InstanceOfData >()) );

			return( true );
		}

		case AVM_ARG_DATA_REF_KIND:
		{
			current( ENV->getRvalue( outED,
					ENV->getRvalue(outED, arg.to_ptr< InstanceOfData >()).
					as_ptr< InstanceOfData >() ));

			return( true );
		}
		case AVM_ARG_DATA_MACRO_KIND:
		{
			current( return_decode_eval_machine(
					ENV->getRvalue(outED, arg.to_ptr< InstanceOfData >()) ));

			return( true );
		}

		case AVM_ARG_DATA_UFI_KIND:
		{
			if( not eval_processor_dma_rvalue_ufi_pointer(bytecode, arg) )
			{
				return( false );
			}
			else if( current().is< RuntimeID >() )
			{
				return( true );
			}
			else if( current().is< InstanceOfMachine >() )
			{
				InstanceOfMachine * aMachine =
						current().to_ptr< InstanceOfMachine >();

				if( aMachine->getExecutable()->hasSingleRuntimeInstance() )
				{
					bytecode.setNopCpu();
					if( (count == 1) && (idx == 0) )
					{
						bytecode.setNopsOperation();
					}

					current( arg = outED->getRuntimeID( aMachine ) );
				}
				else
				{
					current( outED->getRuntimeID( aMachine ) );
				}

				return( true );
			}

			return( false );
		}

		case AVM_ARG_EXPRESSION_RID:
		{
			current( return_decode_eval_machine(arg) );

			return( true );
		}

		case AVM_ARG_EXPRESSION_KIND:
		{
			return( eval_processor_dma_machine(
					bytecode, arg.to_ptr< AvmCode >() ));
		}

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "ARGS_ENV::eval_processor_dma_machine :> "
						"Unexpected argcode << " << bytecode.strCode()
					<< " >> for : " << arg.str() << " !!!"
					<< SEND_EXIT;

			current( arg );

			return( false );
		}
	}
}


bool ARGS_ENV::eval_processor_dma_machine(AvmBytecode & bytecode, AvmCode * aCode)
{
	InstructionEnvironment EVAL_ARG(ENV, outED, aCode->size());
	if( EVAL_ARG.mARG->decode_eval_args_processor(bytecode, aCode) )
	{
		outED = EVAL_ARG.mARG->outED;
	}
	else
	{
		return( false );
	}

	switch( aCode->getAvmOpCode() )
	{
		case AVM_OPCODE_SCHEDULE_IN:
		{
			const BFCode & scheduleCode = outED->getRuntimeFormOnSchedule(
					EVAL_ARG.mARG->at(1).bfRID() );

			current( ExpressionConstructor::newBoolean(
					StatementFactory::containsOperationOnRID(
							scheduleCode, AVM_OPCODE_RUN,
							EVAL_ARG.mARG->at(0).bfRID())) );

			return( true );
		}

		case AVM_OPCODE_STATUS_BEING:
		case AVM_OPCODE_STATUS_IS:
		case AVM_OPCODE_STATUS_WAS:
		case AVM_OPCODE_STATUS_WILL:

		case AVM_OPCODE_INVOKE_NEW:
		{
			EvaluationEnvironment eENV(*ENV, outED, INCR_BF(aCode).bfCode());
			if( eENV.seval(EVAL_ARG.mARG) )
			{
				outED = eENV.outED;

				current( eENV.outVAL );

				return( true );
			}

			return( false );
		}

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "ARGS_ENV::eval_processor_dma_machine :> "
					"Unexpected opcode << " << aCode->strDebug() << " >> !!!"
					<< SEND_EXIT;

			return( false );
		}
	}
}


const RuntimeID & ARGS_ENV::return_decode_eval_machine(const BF & anElement)
{
	switch( anElement.classKind() )
	{
		case FORM_RUNTIME_ID_KIND:
		{
			return( anElement.bfRID() );
		}

		case FORM_INSTANCE_MACHINE_KIND:
		{
			return( outED->getRuntimeID(anElement.to_ptr< InstanceOfMachine >()) );
		}

		case FORM_INSTANCE_DATA_KIND:
		{
			InstanceOfData * anInstance = anElement.to_ptr< InstanceOfData >();

			if( anInstance->isTypedMachine() )
			{
				if( anInstance->getModifier().hasFeatureMutable() )
				{
					const BF & bfInstance = ENV->getRvalue(outED, anInstance);

					if( bfInstance.is< RuntimeID >() )
					{
						return( bfInstance.bfRID() );
					}
					else if( bfInstance.is< InstanceOfMachine >() )
					{
						return( outED->getRuntimeID(
								bfInstance.to_ptr< InstanceOfMachine >()) );
					}
					else if( anInstance->getModifier().anyNatureReferenceMacro()
							&& bfInstance.is< InstanceOfData >()
							&& (bfInstance != anInstance) )
					{
						return( return_decode_eval_machine(ENV->getRvalue(outED,
								bfInstance.to_ptr< InstanceOfData >())) );
					}
					else
					{
						AVM_OS_WARN << "Unexpected" << str_header( anInstance )
							<< " as RuntimeID argument !!!" << std::endl;
					}
				}
				else if( anInstance->getModifier().
							hasModifierPublicFinalStatic() )
				{
					AVM_OS_WARN << "Unexpected " << str_header( anInstance )
							<< " as RuntimeID argument !!!" << std::endl;
				}
				else
				{
					AVM_OS_WARN << "Unexpected " << str_header( anInstance )
							<< " as RuntimeID argument :> bad type data !!!"
							<< std::endl;
				}
			}
			else
			{
				AVM_OS_WARN << "Unexpected " << str_header( anInstance )
						<< " as RuntimeID argument :> bad type data !!!"
						<< std::endl;
			}

			return( RuntimeID::REF_NULL );
		}

		case FORM_AVMCODE_KIND:
		{
			EvaluationEnvironment eENV(*ENV, outED, anElement.bfCode());
			if( eENV.seval() )
			{
				if( eENV.outVAL.is< RuntimeID >() )
				{
					outED = eENV.outED;

					return( eENV.outVAL.bfRID() );
				}
				else
				{
					AVM_OS_WARN << "Unexpected " << eENV.outVAL.str()
						<< " as RuntimeID argument !!!" << std::endl;
				}
			}

			return( RuntimeID::REF_NULL );
		}

		default:
		{
			AVM_OS_EXIT( FAILED )
					<< "ENV::evalMachine:> Unexpected form KIND\n"
					<< anElement.toString()
					<< SEND_EXIT;

			return( RuntimeID::REF_NULL );
		}
	}
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// EVAL PROCESSOR ARITHMETIC / LOGIC
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/**
 * EVAL PROCESSOR < AVM_ARG_ARITHMETIC_LOGIC_CPU >
 */
bool ARGS_ENV::eval_processor_alu(AvmBytecode & bytecode, BF & arg)
{
	switch( bytecode.operand )
	{
		case AVM_ARG_EXPRESSION_KIND:
		{
			return( eval_processor_alu(bytecode, arg.to_ptr< AvmCode >()) );
		}

		case AVM_ARG_STATEMENT_KIND:
		{
			EvaluationEnvironment eENV(*ENV, outED, arg.bfCode());
			if( eENV.seval() )
			{
				outED = eENV.outED;

				current( eENV.outVAL );

				return( true );
			}
			else
			{
				return( false );
			}
		}

		case AVM_ARG_BOOLEAN_KIND:
		case AVM_ARG_INTEGER_KIND:
		case AVM_ARG_RATIONAL_KIND:
		case AVM_ARG_FLOAT_KIND:

		case AVM_ARG_DATA_CST_KIND:

		case AVM_ARG_BUILTIN_KIND:
		case AVM_ARG_BUILTIN_ARRAY_KIND:
		case AVM_ARG_CHARACTER_KIND:
		case AVM_ARG_STRING_KIND:

		case AVM_ARG_PORT_KIND:
		case AVM_ARG_BUFFER_KIND:
		case AVM_ARG_CONNECTOR_KIND:
		{
			current( arg );

			return( true );
		}

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "ARGS_ENV::eval_processor_alu :> Unexpected argcode << "
					<< argsBytecode[idx].strCode() << " >> for : "
					<< arg.str() << " !!!"
					<< SEND_EXIT;

			current( arg );

			return( false );
		}
	}
}


bool ARGS_ENV::eval_processor_alu(AvmBytecode & bytecode, AvmCode * aCode)
{
	InstructionEnvironment EVAL_ARG(ENV, outED, aCode->size());
	if( EVAL_ARG.mARG->decode_eval_args_processor(bytecode, aCode) )
	{
		outED = EVAL_ARG.mARG->outED;
	}
	else
	{
		return( false );
	}

	switch( aCode->getAvmOpCode() )
	{
		case AVM_OPCODE_PLUS:
		{
			current( ExpressionConstructorNative::addExpr(
					*(EVAL_ARG.mARG->values)) );

			return( true );
		}
		case AVM_OPCODE_MINUS:
		{
			current( ExpressionConstructorNative::minusExpr(
					EVAL_ARG.mARG->at(0), EVAL_ARG.mARG->at(1)) );

			return( true );
		}
		case AVM_OPCODE_UMINUS:
		{
			current( ExpressionConstructorNative::uminusExpr(
					EVAL_ARG.mARG->at(0) ) );

			return( true );
		}

		case AVM_OPCODE_MULT:
		{
			current( ExpressionConstructorNative::multExpr(
					*(EVAL_ARG.mARG->values)) );

			return( true );
		}
		case AVM_OPCODE_POW:
		{
			current( ExpressionConstructorNative::powExpr(
					EVAL_ARG.mARG->at(0), EVAL_ARG.mARG->at(1)) );

			return( true );
		}

		case AVM_OPCODE_DIV:
		{
			current( ExpressionConstructorNative::divExpr(
					EVAL_ARG.mARG->at(0), EVAL_ARG.mARG->at(1)) );

			return( true );
		}

//		case AVM_OPCODE_MOD:
//		case AVM_OPCODE_MIN:
//		case AVM_OPCODE_MAX:

		case AVM_OPCODE_EQ:
		{
			current( ExpressionConstructorNative::eqExpr(
					EVAL_ARG.mARG->at(0), EVAL_ARG.mARG->at(1)) );

			return( true );
		}
		case AVM_OPCODE_NEQ:
		{
			current( ExpressionConstructorNative::neqExpr(
					EVAL_ARG.mARG->at(0), EVAL_ARG.mARG->at(1)) );

			return( true );
		}

		case AVM_OPCODE_SEQ:
		{
			current( ExpressionConstructorNative::seqExpr(
					EVAL_ARG.mARG->at(0), EVAL_ARG.mARG->at(1)) );

			return( true );
		}
		case AVM_OPCODE_NSEQ:
		{
			current( ExpressionConstructorNative::nseqExpr(
					EVAL_ARG.mARG->at(0), EVAL_ARG.mARG->at(1)) );

			return( true );
		}

		case AVM_OPCODE_LT:
		{
			current( ExpressionConstructorNative::ltExpr(
					EVAL_ARG.mARG->at(0), EVAL_ARG.mARG->at(1)) );

			return( true );
		}
		case AVM_OPCODE_LTE:
		{
			current( ExpressionConstructorNative::lteExpr(
					EVAL_ARG.mARG->at(0), EVAL_ARG.mARG->at(1)) );

			return( true );
		}
		case AVM_OPCODE_GT:
		{
			current( ExpressionConstructorNative::gtExpr(
					EVAL_ARG.mARG->at(0), EVAL_ARG.mARG->at(1)) );

			return( true );
		}
		case AVM_OPCODE_GTE:
		{
			current( ExpressionConstructorNative::gteExpr(
					EVAL_ARG.mARG->at(0), EVAL_ARG.mARG->at(1)) );

			return( true );
		}



		case AVM_OPCODE_NOT:
		{
			current( ExpressionConstructorNative::notExpr(
					EVAL_ARG.mARG->at(0) ) );

			return( true );
		}

		case AVM_OPCODE_AND:
		{
			current( ExpressionConstructorNative::andExpr(
					*(EVAL_ARG.mARG->values)) );

			return( true );
		}
		case AVM_OPCODE_NAND:
		{
			current( ExpressionConstructorNative::notExpr(
					ExpressionConstructorNative::andExpr(
							*(EVAL_ARG.mARG->values)) ));

			return( true );
		}

//		case AVM_OPCODE_XAND:
//		{
//			return( true );
//		}

		case AVM_OPCODE_OR:
		{
			current( ExpressionConstructorNative::orExpr(
					*(EVAL_ARG.mARG->values)) );

			return( true );
		}
		case AVM_OPCODE_NOR:
		{
			current( ExpressionConstructorNative::notExpr(
					ExpressionConstructorNative::orExpr(
							*(EVAL_ARG.mARG->values)) ));

			return( true );
		}

//		case AVM_OPCODE_XOR:
//		case AVM_OPCODE_XNOR:

		// RANDOM
		case AVM_OPCODE_RANDOM:
		{
			current( ExpressionConstructorNative::newInteger(
					RANDOM::gen_integer(
							EVAL_ARG.mARG->at(0).toInteger(),
							EVAL_ARG.mARG->at(1).toInteger() ) ) );

			return( true );
		}

//		// ROUNDING
//		case AVM_OPCODE_ABS:
//		case AVM_OPCODE_CEIL:
//		case AVM_OPCODE_FLOOR:
//		case AVM_OPCODE_ROUND:
//		case AVM_OPCODE_TRUNCATE:
//
//		// EXP - LOG
//		case AVM_OPCODE_SQRT:
//		case AVM_OPCODE_EXP:
//		case AVM_OPCODE_LN:
//		case AVM_OPCODE_LOG:
//
//		// TRIGONOMETRIC
//		case AVM_OPCODE_SIN:
//		case AVM_OPCODE_COS:
//		case AVM_OPCODE_TAN:
//
//		case AVM_OPCODE_SINH:
//		case AVM_OPCODE_COSH:
//		case AVM_OPCODE_TANH:
//
//		case AVM_OPCODE_ASIN:
//		case AVM_OPCODE_ACOS:
//		case AVM_OPCODE_ATAN:
//		case AVM_OPCODE_ATAN2:
//
//		case AVM_OPCODE_ASINH:
//		case AVM_OPCODE_ACOSH:
//		case AVM_OPCODE_ATANH:

		case AVM_OPCODE_CTOR:
		{
			switch( aCode->getInstruction()->getMainOperand() )
			{
				case AVM_ARG_STRING_KIND:
				{
					current( ExpressionConstructor::newString(
							EVAL_ARG.mARG->at(1).str()) );

					return( true );
				}
				case AVM_ARG_CHARACTER_KIND:
				case AVM_ARG_BOOLEAN_KIND:
				case AVM_ARG_INTEGER_KIND:
				case AVM_ARG_RATIONAL_KIND:
				case AVM_ARG_FLOAT_KIND:

				default:
				{
					current( EVAL_ARG.mARG->at(1) );

					return( true );
				}
			}

			return( true );
		}

		default:
		{
			current( ExpressionConstructorNative::newExpr(
					aCode->getOperator(), *(EVAL_ARG.mARG->values)) );

			return( true );

//			AVM_OS_FATAL_ERROR_EXIT
//					<< "ARGS_ENV::eval_processor_alu :> "
//						"Unexpected opcode << " << aCode->strDebug()
//					<< " >> for : " << aCode->strDebug() << " !!!"
//					<< SEND_EXIT;
//
//			return( false );
		}
	}
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// EVAL PROCESSOR STATEMENT
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/**
 * EVAL PROCESSOR < AVM_ARG_STATEMENT_CPU >
 */
bool ARGS_ENV::eval_processor_statement(AvmBytecode & bytecode, AvmCode * aCode)
{
	InstructionEnvironment EVAL_ARG(ENV, outED, aCode->size());
	if( EVAL_ARG.mARG->main_decode_eval_args(aCode) )
	{
		outED = EVAL_ARG.mARG->outED;
	}
	else
	{
		return( aCode );
	}

	switch( aCode->getAvmOpCode() )
	{
		case AVM_OPCODE_OBS:
		{
			current( EVAL_ARG.mARG->at(2) );

			return( true );
		}


		case AVM_OPCODE_INPUT:
		case AVM_OPCODE_OUTPUT:
		{
			BFCode ioTrace = ENV->searchTraceIO(outED->getIOElementTrace(), aCode);

			if( ioTrace.valid() )
			{
				current( ioTrace );

				AvmCode::iterator traceArg = ioTrace->begin();
				EVAL_ARG.mARG->begin(1);
				for( ++traceArg ; EVAL_ARG.mARG->hasNext() ;
						EVAL_ARG.mARG->next() , ++traceArg )
				{
					if( not ENV->setRvalue( outED, EVAL_ARG.mARG->current().
							as_ptr< InstanceOfData >(), (*traceArg)) )
					{
						return( false );
					}
				}

				return( true );
			}

			return( false );
		}

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "ARGS_ENV::eval_processor_statement :> "
						"Unexpected bytecode << " << bytecode.strCode()
					<< " >> for : " << aCode->strDebug() << " !!!"
					<< SEND_EXIT;

			return( false );
		}
	}

	return( false );
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// EVAL PROCESSOR CHARACTER
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/**
 * EVAL PROCESSOR < AVM_ARG_CHARACTER_CPU >
 */
bool ARGS_ENV::eval_processor_character(AvmBytecode & bytecode, BF & arg)
{
	switch( bytecode.operand )
	{
		case AVM_ARG_EXPRESSION_KIND:
		{
			return( eval_processor_character( bytecode, arg.to_ptr< AvmCode >() ) );
		}

		case AVM_ARG_CHARACTER_KIND:
		{
			current( arg );

			return( true );
		}

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "ARGS_ENV::eval_processor_character :> "
						"Unexpected argcode << " << bytecode.strCode()
					<< " >> for : " << arg.str() << " !!!"
					<< SEND_EXIT;

			current( ExpressionConstructor::newString(arg.str()) );

			return( true );
		}
	}
}


bool ARGS_ENV::eval_processor_character(AvmBytecode & bytecode, AvmCode * aCode)
{
	InstructionEnvironment EVAL_ARG(ENV, outED, aCode->size());
	if( EVAL_ARG.mARG->main_decode_eval_args(aCode) )
	{
		outED = EVAL_ARG.mARG->outED;
	}
	else
	{
		return( aCode );
	}

	switch( aCode->getAvmOpCode() )
	{
		case AVM_OPCODE_CTOR:
		{
			switch( aCode->getInstruction()->getMainOperand() )
			{
				case AVM_ARG_STRING_KIND:
				{
					if( EVAL_ARG.mARG->at(1).is< Character >() )
					{
						current( ExpressionConstructor::newString(
								to_string(EVAL_ARG.mARG->at(1).to_ptr<
										Character >()->getValue())) );
					}
					else
					{
						current( ExpressionConstructor::newString(
								EVAL_ARG.mARG->at(1).str()) );
					}

					return( true );
				}
				case AVM_ARG_CHARACTER_KIND:
				{
					current( ExpressionConstructor::newChar(
							EVAL_ARG.mARG->at(1).str().at(0) ) );

					return( true );
				}

				case AVM_ARG_BOOLEAN_KIND:
				case AVM_ARG_INTEGER_KIND:
				case AVM_ARG_RATIONAL_KIND:
				case AVM_ARG_FLOAT_KIND:


				default:
				{
					current( ExpressionConstructor::newString(
							EVAL_ARG.mARG->at(1).str() ));

					return( true );
				}
			}

			return( true );
		}

//		case AVM_OPCODE_EMPTY:
//		{
//			current( ExpressionConstructor::newBoolean( false ) );
//
//			return( true );
//		}
//
//		case AVM_OPCODE_NONEMPTY:
//		{
//			current( ExpressionConstructor::newBoolean( true ) );
//
//			return( true );
//		}
//		case AVM_OPCODE_SINGLETON:
//		{
//			current( ExpressionConstructor::newBoolean( true ) );
//
//			return( true );
//		}
//		case AVM_OPCODE_POPULATED:
//		{
//			current( ExpressionConstructor::newBoolean( false ) );
//
//			return( true );
//		}
//
//		case AVM_OPCODE_SIZE:
//		{
//			current( ExpressionConstructor::INTEGER_ONE );
//
//			return( true );
//		}

		case AVM_OPCODE_EQ:
		case AVM_OPCODE_SEQ:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(0).to_ptr< Character >()->getValue() ==
					EVAL_ARG.mARG->at(1).to_ptr< Character >()->getValue() ));

			return( true );
		}
		case AVM_OPCODE_NEQ:
		case AVM_OPCODE_NSEQ:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(0).to_ptr< Character >()->getValue() !=
					EVAL_ARG.mARG->at(1).to_ptr< Character >()->getValue() ));

			return( true );
		}

		case AVM_OPCODE_LT:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(0).to_ptr< Character >()->getValue() <
					EVAL_ARG.mARG->at(1).to_ptr< Character >()->getValue() ));

			return( true );
		}
		case AVM_OPCODE_LTE:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(0).to_ptr< Character >()->getValue() <=
					EVAL_ARG.mARG->at(1).to_ptr< Character >()->getValue() ));

			return( true );
		}
		case AVM_OPCODE_GT:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(0).to_ptr< Character >()->getValue() >
					EVAL_ARG.mARG->at(1).to_ptr< Character >()->getValue() ));

			return( true );
		}
		case AVM_OPCODE_GTE:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(0).to_ptr< Character >()->getValue() >=
					EVAL_ARG.mARG->at(1).to_ptr< Character >()->getValue() ));

			return( true );
		}


		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "ARGS_ENV::eval_processor_character :> "
						"Unexpected bytecode << " << bytecode.strCode()
					<< " >> for : " << aCode->strDebug() << " !!!"
					<< SEND_EXIT;

			return( false );
		}
	}
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// EVAL PROCESSOR STRING
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/**
 * EVAL PROCESSOR < AVM_ARG_STRING_CPU >
 */
bool ARGS_ENV::eval_processor_string(AvmBytecode & bytecode, BF & arg)
{
	switch( bytecode.operand )
	{
		case AVM_ARG_EXPRESSION_KIND:
		{
			return( eval_processor_string( bytecode, arg.to_ptr< AvmCode >() ) );
		}

		case AVM_ARG_STRING_KIND:
		{
			current( arg );

			return( true );
		}

		case AVM_ARG_CHARACTER_KIND:
		{
			current( ExpressionConstructor::newString(
					to_string(arg.to_ptr< Character >()->getValue())) );

			return( true );
		}

		case AVM_ARG_BOOLEAN_KIND:
		case AVM_ARG_INTEGER_KIND:
		case AVM_ARG_RATIONAL_KIND:
		case AVM_ARG_FLOAT_KIND:
		case AVM_ARG_OPERATOR_KIND:
		case AVM_ARG_BUILTIN_KIND:
		{
			current( ExpressionConstructor::newString( arg.str() ) );

			return( true );
		}


		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "ARGS_ENV::eval_processor_string :> "
						"Unexpected argcode << " << bytecode.strCode()
					<< " >> for : " << arg.str() << " !!!"
					<< SEND_EXIT;

			current( ExpressionConstructor::newString(arg.str()) );

			return( true );
		}
	}
}


bool ARGS_ENV::eval_processor_string(AvmBytecode & bytecode, AvmCode * aCode)
{
	InstructionEnvironment EVAL_ARG(ENV, outED, aCode->size());
	if( EVAL_ARG.mARG->main_decode_eval_args(aCode) )
	{
		outED = EVAL_ARG.mARG->outED;
	}
	else
	{
		return( aCode );
	}

	switch( aCode->getAvmOpCode() )
	{
		case AVM_OPCODE_PLUS:
		case AVM_OPCODE_CONCAT:
		{
			std::ostringstream oss;
			for( EVAL_ARG.mARG->begin() ; EVAL_ARG.mARG->hasNext() ;
					EVAL_ARG.mARG->next() )
			{
				oss << EVAL_ARG.mARG->current().to_ptr< String >()->getValue();
			}

			current( ExpressionConstructor::newString(oss.str()) );

			return( true );
		}

		case AVM_OPCODE_REMOVE:
		{
			std::string val = EVAL_ARG.mARG->at(0).to_ptr< String >()->getValue();

			StringTools::replaceAll(val,
					EVAL_ARG.mARG->at(1).to_ptr< String >()->getValue(), "");

			current( ExpressionConstructor::newString( val ) );

			return( true );
		}

		case AVM_OPCODE_CTOR:
		{
			switch( aCode->getInstruction()->getMainOperand() )
			{
				case AVM_ARG_STRING_KIND:
				{
					current( ExpressionConstructor::newString(
							EVAL_ARG.mARG->at(1).str()) );

					return( true );
				}
				case AVM_ARG_CHARACTER_KIND:
				{
					if( EVAL_ARG.mARG->at(1).to_ptr< String >()
							->getValue().empty() )
					{
						return( false );
					}

					current( ExpressionConstructor::newChar( EVAL_ARG.mARG
							->at(1).to_ptr< String >()->getValue().at(0)) );

					return( true );
				}

				case AVM_ARG_BOOLEAN_KIND:
				{
					current( ExpressionConstructor::newBoolean( EVAL_ARG.mARG
							->at(1).to_ptr< String >()->getValue()) );

					return( true );
				}
				case AVM_ARG_INTEGER_KIND:
				{
					current( ExpressionConstructor::newInteger( EVAL_ARG.mARG
							->at(1).to_ptr< String >()->getValue()) );

					return( true );
				}
				case AVM_ARG_RATIONAL_KIND:
				{
					current( ExpressionConstructor::newRational( EVAL_ARG.mARG
							->at(1).to_ptr< String >()->getValue()) );

					return( true );
				}
				case AVM_ARG_FLOAT_KIND:
				{
					current( ExpressionConstructor::newFloat( EVAL_ARG.mARG
							->at(1).to_ptr< String >()->getValue()) );

					return( true );
				}

				default:
				{
					current( ExpressionConstructor::newString(
							EVAL_ARG.mARG->at(1).str() ));

					return( true );
				}
			}

			return( true );
		}

		case AVM_OPCODE_CONTAINS:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(0).to_ptr< String >()->getValue().find(
							EVAL_ARG.mARG->at(1).to_ptr< String >()
									->getValue() ) != std::string::npos  ));

			return( true );
		}

		case AVM_OPCODE_IN:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(1).to_ptr< String >()->getValue().find(
							EVAL_ARG.mARG->at(0).to_ptr< String >()
									->getValue() ) != std::string::npos  ));

			return( true );
		}
		case AVM_OPCODE_NOTIN:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(1).to_ptr< String >()->getValue().find(
							EVAL_ARG.mARG->at(0).to_ptr< String >()
									->getValue() ) == std::string::npos  ));

			return( true );
		}

		case AVM_OPCODE_STARTS_WITH:
		{
			current( ExpressionConstructor::newBoolean( StringTools::startsWith(
					EVAL_ARG.mARG->at(0).to_ptr< String >()->getValue(),
					EVAL_ARG.mARG->at(1).to_ptr< String >()->getValue() )));

			return( true );
		}
		case AVM_OPCODE_ENDS_WITH:
		{
			current( ExpressionConstructor::newBoolean( StringTools::endsWith(
					EVAL_ARG.mARG->at(0).to_ptr< String >()->getValue(),
					EVAL_ARG.mARG->at(1).to_ptr< String >()->getValue() )));

			return( true );
		}

		case AVM_OPCODE_EMPTY:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(0)
						.to_ptr< String >()->getValue().empty() ) );

			return( true );
		}

		case AVM_OPCODE_NONEMPTY:
		{
			current( ExpressionConstructor::newBoolean(
					not EVAL_ARG.mARG->at(0)
						.to_ptr< String >()->getValue().empty() ) );

			return( true );
		}
		case AVM_OPCODE_SINGLETON:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(0)
						.to_ptr< String >()->getValue().size() == 1 ) );

			return( true );
		}
		case AVM_OPCODE_POPULATED:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(0)
						.to_ptr< String >()->getValue().size() > 1 ) );

			return( true );
		}

		case AVM_OPCODE_SIZE:
		{
			current( ExpressionConstructor::newUInteger(
					EVAL_ARG.mARG->at(0)
						.to_ptr< String >()->getValue().size() ) );

			return( true );
		}

		case AVM_OPCODE_EQ:
		case AVM_OPCODE_SEQ:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(0).to_ptr< String >()->getValue().compare(
					EVAL_ARG.mARG->at(1).to_ptr< String >()->getValue()) == 0 ));

			return( true );
		}
		case AVM_OPCODE_NEQ:
		case AVM_OPCODE_NSEQ:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(0).to_ptr< String >()->getValue().compare(
					EVAL_ARG.mARG->at(1).to_ptr< String >()->getValue()) != 0 ) );

			return( true );
		}

		case AVM_OPCODE_LT:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(0).to_ptr< String >()->getValue().compare(
					EVAL_ARG.mARG->at(1).to_ptr< String >()->getValue()) < 0 ) );

			return( true );
		}
		case AVM_OPCODE_LTE:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(0).to_ptr< String >()->getValue().compare(
					EVAL_ARG.mARG->at(1).to_ptr< String >()->getValue()) <= 0 ) );

			return( true );
		}
		case AVM_OPCODE_GT:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(0).to_ptr< String >()->getValue().compare(
					EVAL_ARG.mARG->at(1).to_ptr< String >()->getValue()) > 0 ) );

			return( true );
		}
		case AVM_OPCODE_GTE:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(0).to_ptr< String >()->getValue().compare(
					EVAL_ARG.mARG->at(1).to_ptr< String >()->getValue()) >= 0 ) );

			return( true );
		}


		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "ARGS_ENV::eval_processor_string :> "
						"Unexpected bytecode << " << bytecode.strCode()
					<< " >> for : " << aCode->strDebug() << " !!!"
					<< SEND_EXIT;

			return( false );
		}
	}
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// EVAL PROCESSOR ARRAY
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/**
 * EVAL PROCESSOR < AVM_ARG_ARRAY_[L|V]_CPU >
 */
bool ARGS_ENV::eval_processor_array_lvalue(AvmBytecode & bytecode, BF & arg)
{
	switch( bytecode.operand )
	{
		case AVM_ARG_ARRAY_KIND:
		{
			ArrayBF & argArray = arg.as_ref< ArrayBF >();

			ArrayBF * outArray = new ArrayBF(
					argArray.getTypeSpecifier(), argArray.size());

			if( argArray.hasInstruction() )
			{
				AvmInstruction * instruction = argArray.getInstruction();
				for( avm_size_t offset = 0 ; offset < argArray.size() ; ++offset )
				{
					outArray->set(offset, return_decode_eval_processor(
							instruction->at(offset), argArray[offset]));
				}
			}
			else
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "ARGS_ENV::eval_processor_array_lvalue :> "
							"Unexpected array without instruction << "
						<< bytecode.strCode() << " >> for : << "
						<< arg.str() << " !!!"
						<< SEND_EXIT;

				return( false );
			}

			current( BF( outArray ) );

			return( true );
		}

		case AVM_ARG_BUILTIN_ARRAY_KIND:
		{
			current( arg );

			return( true );
		}

		case AVM_ARG_EXPRESSION_KIND:
		{
			BF value = return_decode_eval_processor(
					arg.to_ptr< AvmCode >()
						->getInstruction()->getMainBytecode(), arg);

			current( genArray(
					bytecode.dtype->as< ContainerTypeSpecifier >(), value) );

			return( true );
		}

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "ARGS_ENV::eval_processor_array_lvalue :> "
						"Unexpected argcode << " << bytecode.strCode()
					<< " >> for : << " << arg.str() << " !!!"
					<< SEND_EXIT;

			current( genArray(
					bytecode.dtype->as< ContainerTypeSpecifier >(), arg) );

			return( false );
		}
	}
}


bool ARGS_ENV::eval_processor_array_rvalue(AvmBytecode & bytecode, BF & arg)
{
	switch( bytecode.operand )
	{
		case AVM_ARG_ARRAY_KIND:
		{
			ArrayBF & argArray = arg.as_ref< ArrayBF >();

			ArrayBF * outArray = new ArrayBF(
					argArray.getTypeSpecifier(), argArray.size());

			if( argArray.hasInstruction() )
			{
				AvmInstruction * instruction = argArray.getInstruction();
				for( avm_size_t offset = 0 ; offset < argArray.size() ; ++offset )
				{
					outArray->set(offset, return_decode_eval_processor(
							instruction->at(offset), argArray[offset]));
				}
			}
			else
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "ARGS_ENV::eval_processor_array_rvalue :> "
							"Unexpected array without instruction << "
						<< bytecode.strCode() << " >> for : << "
						<< arg.str() << " !!!"
						<< SEND_EXIT;

				return( false );
			}

			current( BF( outArray ) );

			return( true );
		}

		case AVM_ARG_BUILTIN_ARRAY_KIND:
		{
			current( arg );

			return( true );
		}

		case AVM_ARG_BOOLEAN_KIND:
		case AVM_ARG_INTEGER_KIND:
		case AVM_ARG_RATIONAL_KIND:
		case AVM_ARG_FLOAT_KIND:

		case AVM_ARG_BUILTIN_KIND:
		case AVM_ARG_CHARACTER_KIND:
		case AVM_ARG_STRING_KIND:

		case AVM_ARG_PORT_KIND:
		case AVM_ARG_BUFFER_KIND:
		case AVM_ARG_CONNECTOR_KIND:

		case AVM_ARG_DATA_CST_KIND:
		{
			current( genArray(
					bytecode.dtype->as< ContainerTypeSpecifier >(), arg) );


			return( true );
		}

		case AVM_ARG_DATA_KIND:
		{
			current( genArray( bytecode.dtype->as< ContainerTypeSpecifier >(),
					ENV->getRvalue(outED, arg.to_ptr< InstanceOfData >()) ));

			return( true );
		}

		case AVM_ARG_DATA_REF_KIND:
		{
			current( genArray( bytecode.dtype->as< ContainerTypeSpecifier >(),
					ENV->getRvalue(outED, ENV->getRvalue(outED, arg.to_ptr<
							InstanceOfData >()).to_ptr< InstanceOfData >()) ));

			return( true );
		}

		case AVM_ARG_DATA_MACRO_KIND:
		{
			BF rvalue  = ENV->getRvalue(outED, arg.to_ptr< InstanceOfData >());

			if( rvalue.is< InstanceOfData >() )
			{
				rvalue = ENV->getRvalue(outED, rvalue.to_ptr< InstanceOfData >());
			}
			else
			{
				if( decode_eval_rvalue( rvalue ) )
				{
					rvalue = current();
				}
				else
				{
					return( false );
				}
			}

			current( genArray(
					bytecode.dtype->as< ContainerTypeSpecifier >(), rvalue ));

			return( true );
		}

		case AVM_ARG_DATA_UFI_KIND:
		{
			if( eval_processor_dma_rvalue_ufi_pointer(bytecode, arg) )
			{
				current( genArray( bytecode.dtype->as<
						ContainerTypeSpecifier >(), current() ) );

				return( true );
			}

			return( false );
		}

		case AVM_ARG_MACHINE_RID:
		case AVM_ARG_EXPRESSION_RID:
		case AVM_ARG_SELF_RID:
		case AVM_ARG_PARENT_RID:
		case AVM_ARG_COMMUNICATOR_RID:
		case AVM_ARG_SYSTEM_RID:
		case AVM_ARG_ENVIRONMENT_RID:
		case AVM_ARG_COMPONENT_SELF_RID:
		case AVM_ARG_COMPONENT_PARENT_RID:
		case AVM_ARG_COMPONENT_COMMUNICATOR_RID:
		{
			current( genArray( bytecode.dtype->as< ContainerTypeSpecifier >(),
					return_decode_eval_machine( arg ) ));


			return( true );
		}


		case AVM_ARG_EXPRESSION_KIND:
		{
			return( eval_processor_array_rvalue(
					bytecode, arg.to_ptr< AvmCode >() ) );
		}


		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "ARGS_ENV::eval_processor_array_rvalue :> "
						"Unexpected argcode << " << bytecode.strCode()
					<< " >> for : " << arg.str() << " !!!"
					<< SEND_EXIT;

			current( genArray(
					bytecode.dtype->as< ContainerTypeSpecifier >(), arg) );

			return( false );
		}
	}
}


BF ARGS_ENV::genArray(ContainerTypeSpecifier * arrayT, const BF & arg)
{
	BF value = ( arrayT->getContentsTypeSpecifier().isTypedArray() )?
			genArray( arrayT->getContentsTypeSpecifier().rawContainer(), arg )
			: arg;

	return( BF( new ArrayBF(arrayT, value) ) );
}



bool ARGS_ENV::eval_processor_array_rvalue(AvmBytecode & bytecode, AvmCode * aCode)
{
	InstructionEnvironment EVAL_ARG(ENV, outED, aCode->size());
	if( EVAL_ARG.mARG->main_decode_eval_args(aCode) )
	{
		outED = EVAL_ARG.mARG->outED;
	}
	else
	{
		return( aCode );
	}

	switch( aCode->getAvmOpCode() )
	{
		case AVM_OPCODE_CONCAT:
		{
			const ArrayBF & arg1Array = EVAL_ARG.mARG->at(0).as_ref< ArrayBF >();
			const ArrayBF & arg2Array = EVAL_ARG.mARG->at(1).as_ref< ArrayBF >();

			ArrayBF * outArray = new ArrayBF( arg1Array.getTypeSpecifier(),
					arg1Array.size() + arg2Array.size() );

			avm_size_t offset = 0;
			for( ; offset < arg1Array.size() ; ++offset )
			{
				outArray->set(offset, arg1Array[offset]);
			}

			for( avm_size_t pos = 0 ; pos < arg2Array.size() ; ++pos , ++offset )
			{
				outArray->set(offset, arg2Array[pos]);
			}

			current( BF( outArray ) );

			return( true );
		}

		case AVM_OPCODE_REMOVE:
		{
			const ArrayBF & arg1Array = EVAL_ARG.mARG->at(0).as_ref< ArrayBF >();

			ArrayBF * outArray = new ArrayBF(
					arg1Array.getTypeSpecifier(), arg1Array.size() );

			avm_size_t offset = 0;
			for( avm_size_t pos = 0 ; pos < arg1Array.size() ; ++pos )
			{
				if( arg1Array[pos] == EVAL_ARG.mARG->at(1) )
				{
					outArray->set(offset, arg1Array[offset]);
					++offset;
				}
			}
			outArray->resize( offset );

			current( BF( outArray ) );

			return( true );
		}

//		case AVM_OPCODE_CTOR:
//		{
//			BF value = return_decode_eval_processor(
//					aCode->getInstruction()->getMainBytecode(), arg);
//
//			current( genArray(
//					bytecode.dtype->as< ContainerTypeSpecifier >(), value) );
//
//			return( true );
//		}

		case AVM_OPCODE_CONTAINS:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(0).as_ref< ArrayBF >().contains(
							EVAL_ARG.mARG->at(1)) ));

			return( true );
		}

		case AVM_OPCODE_IN:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(1).as_ref< ArrayBF >().contains(
							EVAL_ARG.mARG->at(0)) ));

			return( true );
		}
		case AVM_OPCODE_NOTIN:
		{
			current( ExpressionConstructor::newBoolean( not
					EVAL_ARG.mARG->at(1).as_ref< ArrayBF >().contains(
							EVAL_ARG.mARG->at(0)) ));

			return( true );
		}

		case AVM_OPCODE_STARTS_WITH:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(0).as_ref< ArrayBF >().startsWith(
					EVAL_ARG.mARG->at(1).as_ref< ArrayBF >()) ));

			return( true );
		}
		case AVM_OPCODE_ENDS_WITH:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(0).as_ref< ArrayBF >().endsWith(
					EVAL_ARG.mARG->at(1).as_ref< ArrayBF >()) ));

			return( true );
		}

		case AVM_OPCODE_EMPTY:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(0).as_ref< ArrayBF >().empty() ) );

			return( true );
		}

		case AVM_OPCODE_NONEMPTY:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(0).as_ref< ArrayBF >().nonempty() ) );

			return( true );
		}
		case AVM_OPCODE_SINGLETON:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(0).as_ref< ArrayBF >().singleton() ) );

			return( true );
		}
		case AVM_OPCODE_POPULATED:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(0).as_ref< ArrayBF >().populated() ) );

			return( true );
		}

		case AVM_OPCODE_SIZE:
		{
			current( ExpressionConstructor::newUInteger(
					EVAL_ARG.mARG->at(0).as_ref< ArrayBF >().size() ) );

			return( true );
		}


		case AVM_OPCODE_EQ:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(0).as_ref< ArrayBF >().isEQ(
					EVAL_ARG.mARG->at(1).as_ref< ArrayBF >()) ));

			return( true );
		}
		case AVM_OPCODE_SEQ:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(0).as_ref< ArrayBF >().isSEQ(
					EVAL_ARG.mARG->at(1).as_ref< ArrayBF >()) ));

			return( true );
		}


		case AVM_OPCODE_NEQ:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(0).as_ref< ArrayBF >().isNEQ(
					EVAL_ARG.mARG->at(1).as_ref< ArrayBF >()) ));

			return( true );
		}
		case AVM_OPCODE_NSEQ:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(0).as_ref< ArrayBF >().isNSEQ(
					EVAL_ARG.mARG->at(1).as_ref< ArrayBF >()) ));

			return( true );
		}

//		case AVM_OPCODE_LT:
//		{
//			current( ExpressionConstructor::newBoolean(
//					EVAL_ARG.mARG->at(0).as_ref< ArrayBF >().isLT(
//					EVAL_ARG.mARG->at(1).as_ref< ArrayBF >()) ));
//
//			return( true );
//		}
//		case AVM_OPCODE_LTE:
//		{
//			current( ExpressionConstructor::newBoolean(
//					EVAL_ARG.mARG->at(0).as_ref< ArrayBF >().isLTE(
//					EVAL_ARG.mARG->at(1).as_ref< ArrayBF >()) ));
//
//			return( true );
//		}
//
//		case AVM_OPCODE_GT:
//		{
//			current( ExpressionConstructor::newBoolean(
//					EVAL_ARG.mARG->at(0).as_ref< ArrayBF >().isGT(
//					EVAL_ARG.mARG->at(1).as_ref< ArrayBF >()) ));
//
//			return( true );
//		}
//		case AVM_OPCODE_GTE:
//		{
//			current( ExpressionConstructor::newBoolean(
//					EVAL_ARG.mARG->at(0).as_ref< ArrayBF >().isGTE(
//					EVAL_ARG.mARG->at(1).as_ref< ArrayBF >()) ));
//
//			return( true );
//		}


		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "ARGS_ENV::eval_processor_string :> "
						"Unexpected bytecode << " << bytecode.strCode()
					<< " >> for : " << aCode->strDebug() << " !!!"
					<< SEND_EXIT;

			return( false );
		}
	}
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// EVAL PROCESSOR QUEUE
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/**
 * EVAL PROCESSOR < AVM_ARG_COLLECTION_CPU >
 */
bool ARGS_ENV::eval_processor_vector(AvmBytecode & bytecode, BF & arg)
{
	switch( bytecode.operand )
	{
		case AVM_ARG_EXPRESSION_KIND:
		{
			return( eval_processor_vector(
					bytecode, arg.to_ptr< AvmCode >() ));
		}

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "ARGS_ENV::eval_processor_queue :> "
						"Unexpected bytecode << " << bytecode.strCode()
					<< " >> for : " << arg.str() << " !!!"
					<< SEND_EXIT;

			current( arg );

			return( false );
		}
	}
}


bool ARGS_ENV::eval_processor_vector(AvmBytecode & bytecode, AvmCode * aCode)
{
	InstructionEnvironment EVAL_ARG(ENV, outED, aCode->size());
	if( EVAL_ARG.mARG->main_decode_eval_args(aCode) )
	{
		outED = EVAL_ARG.mARG->outED;
	}
	else
	{
		return( aCode );
	}

	switch( aCode->getAvmOpCode() )
	{
		case AVM_OPCODE_CONTAINS:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(0).to_ptr< BuiltinVector >()
					->contains( EVAL_ARG.mARG->at(1) ) ));

			return( true );
		}

		case AVM_OPCODE_IN:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(1).to_ptr< BuiltinVector >()
					->contains( EVAL_ARG.mARG->at(0) ) ));

			return( true );
		}
		case AVM_OPCODE_NOTIN:
		{
			current( ExpressionConstructor::newBoolean( not
					EVAL_ARG.mARG->at(1).to_ptr< BuiltinVector >()
					->contains( EVAL_ARG.mARG->at(0) ) ));

			return( true );
		}

//		case AVM_OPCODE_STARTS_WITH:
//		{
//			current( ExpressionConstructor::newBoolean( StringTools::startsWith(
//					EVAL_ARG.mARG->at(0).to_ptr< BuiltinVector >()->getValue(),
//					EVAL_ARG.mARG->at(1).to_ptr< BuiltinVector >()->getValue() )));
//
//			return( true );
//		}
//		case AVM_OPCODE_ENDS_WITH:
//		{
//			current( ExpressionConstructor::newBoolean( StringTools::endsWith(
//					EVAL_ARG.mARG->at(0).to_ptr< BuiltinVector >()->getValue(),
//					EVAL_ARG.mARG->at(1).to_ptr< BuiltinVector >()->getValue() )));
//
//			return( true );
//		}

		case AVM_OPCODE_EMPTY:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(0)
						.to_ptr< BuiltinVector >()->empty() ) );

			return( true );
		}

		case AVM_OPCODE_NONEMPTY:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(0)
						.to_ptr< BuiltinVector >()->nonempty() ) );

			return( true );
		}
		case AVM_OPCODE_SINGLETON:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(0)
						.to_ptr< BuiltinVector >()->singleton() ) );

			return( true );
		}
		case AVM_OPCODE_POPULATED:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(0)
						.to_ptr< BuiltinVector >()->populated() ) );

			return( true );
		}

		case AVM_OPCODE_SIZE:
		{
			current( ExpressionConstructor::newUInteger(
					EVAL_ARG.mARG->at(0)
						.to_ptr< BuiltinVector >()->size() ) );

			return( true );
		}

//		case AVM_OPCODE_EQ:
//		case AVM_OPCODE_SEQ:
//		{
//			current( ExpressionConstructor::newBoolean(
//					EVAL_ARG.mARG->at(0).to_ptr< BuiltinVector >()->getValue().compare(
//					EVAL_ARG.mARG->at(1).to_ptr< BuiltinVector >()->getValue()) == 0 ));
//
//			return( true );
//		}
//		case AVM_OPCODE_NEQ:
//		case AVM_OPCODE_NSEQ:
//		{
//			current( ExpressionConstructor::newBoolean(
//					EVAL_ARG.mARG->at(0).to_ptr< BuiltinVector >()->getValue().compare(
//					EVAL_ARG.mARG->at(1).to_ptr< BuiltinVector >()->getValue()) != 0 ) );
//
//			return( true );
//		}
//
//		case AVM_OPCODE_POP:
//		case AVM_OPCODE_PUSH:
//		case AVM_OPCODE_ASSIGN_TOP:
//		{
//			std::ostringstream oss;
//			for( begin() ; hasNext() ; next() )
//			{
//				oss << current().to_ptr< BuiltinVector >()->getValue();
//			}
//
//			current( ExpressionConstructor::newString(oss.str()) );
//
//			return( true );
//		}


		case AVM_OPCODE_APPEND:
		{
			BuiltinVector * bVector =
					EVAL_ARG.mARG->at(0).to_ptr< BuiltinVector >();
			for( EVAL_ARG.mARG->begin(1) ; EVAL_ARG.mARG->hasNext() ;
					EVAL_ARG.mARG->next() )
			{
				if( not bVector->add( EVAL_ARG.mARG->current() ) )
				{
AVM_IF_DEBUG_FLAG( STATEMENT)
	AVM_OS_TRACE << "THROW UNSATISFIED << APPEND >> : "
			<<  outED->mRID.strUniqId() << " |=> "
			<< aCode->str() << std::endl;
	AVM_OS_TRACE << "\t" << "<capacity:" << bVector->capacity()
			<< "> " << bVector->str() << " <=< "
			<< EVAL_ARG.mARG->current().str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT)

					return( false );
				}
			}

			current( EVAL_ARG.mARG->at(0) );

AVM_IF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )
			AVM_OS_TRACE << "rvalue:> " << bVector->str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )

			return( true );
		}

		case AVM_OPCODE_REMOVE:
		{
			BuiltinVector * bVector =
					EVAL_ARG.mARG->at(0).to_ptr< BuiltinVector >();
			for( EVAL_ARG.mARG->begin(1) ; EVAL_ARG.mARG->hasNext() ;
					EVAL_ARG.mARG->next() )
			{
				bVector->remove( EVAL_ARG.mARG->current() );
			}

			current( EVAL_ARG.mARG->at(0) );

AVM_IF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )
	AVM_OS_TRACE << "rvalue:> " << bVector->str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )

			return( true );
		}


		case AVM_OPCODE_CTOR:
		{
			BuiltinContainer * containerValue = BuiltinContainer::create(
					EVAL_ARG.mARG->at(0).as_ptr< ContainerTypeSpecifier >() );

			ArrayBF * arrayValue = EVAL_ARG.mARG->at(1).as_ptr< ArrayBF >();

			containerValue->copy( arrayValue, std::min(
					containerValue->capacity(), arrayValue->size()) );

			current( BF( containerValue ) );

			return( true );
		}

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "ARGS_ENV::eval_processor_queue :> "
						"Unexpected bytecode << " << bytecode.strCode()
					<< " >> for : " << aCode->strDebug() << " !!!"
					<< SEND_EXIT;

			return( false );
		}
	}
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// EVAL PROCESSOR COLLECTION
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/**
 * EVAL PROCESSOR < AVM_ARG_COLLECTION_CPU >
 */
bool ARGS_ENV::eval_processor_collection(AvmBytecode & bytecode, BF & arg)
{
	switch( bytecode.operand )
	{
		case AVM_ARG_EXPRESSION_KIND:
		{
			return( eval_processor_collection(
					bytecode, arg.to_ptr< AvmCode >() ));
		}

		case AVM_ARG_BUILTIN_CONTAINER_KIND:
		{
			current( arg );

			return( true );
		}

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "ARGS_ENV::eval_processor_collection :> "
						"Unexpected bytecode << " << bytecode.strCode()
					<< " >> for : " << arg.str() << " !!!"
					<< SEND_EXIT;

			current( arg );

			return( false );
		}
	}
}


bool ARGS_ENV::eval_processor_collection(AvmBytecode & bytecode, AvmCode * aCode)
{
	InstructionEnvironment EVAL_ARG(ENV, outED, aCode->size());
	if( EVAL_ARG.mARG->main_decode_eval_args(aCode) )
	{
		outED = EVAL_ARG.mARG->outED;
	}
	else
	{
		return( aCode );
	}

	switch( aCode->getAvmOpCode() )
	{
		case AVM_OPCODE_CONTAINS:
		{
			BuiltinCollection * aCollection =
					EVAL_ARG.mARG->at(0).to_ptr< BuiltinCollection >();

			if( aCollection->contains( EVAL_ARG.mARG->at(1) ) )
			{
				current( ExpressionConstructor::newBoolean(true) );
			}
			else
			{
				if( aCollection->singleton() )
				{
					current( ExpressionConstructor::eqExpr(
							aCollection->at(0), EVAL_ARG.mARG->at(1)) );
				}
				else if( aCollection->populated() )
				{
					current( ExpressionConstructor::newExpr(
							OperatorManager::OPERATOR_CONTAINS,
							EVAL_ARG.mARG->at(0), EVAL_ARG.mARG->at(1)) );
				}

				else
				{
					current( ExpressionConstructor::newBoolean(false) );
				}
			}

//			current( ExpressionConstructor::newBoolean(
//					EVAL_ARG.mARG->at(0).to_ptr< BuiltinCollection >()
//					->contains( EVAL_ARG.mARG->at(1) ) ));

			return( true );
		}

		case AVM_OPCODE_IN:
		{
			BuiltinCollection * aCollection =
					EVAL_ARG.mARG->at(1).to_ptr< BuiltinCollection >();

			if( aCollection->contains( EVAL_ARG.mARG->at(0) ) )
			{
				current( ExpressionConstructor::newBoolean(true) );
			}
			else
			{
				if( aCollection->singleton() )
				{
					current( ExpressionConstructor::eqExpr(
							aCollection->at(0), EVAL_ARG.mARG->at(0)) );
				}
				else if( aCollection->populated() )
				{
					current( ExpressionConstructor::newExpr(
							OperatorManager::OPERATOR_CONTAINS,
							EVAL_ARG.mARG->at(1), EVAL_ARG.mARG->at(0)) );
				}
				else
				{
					current( ExpressionConstructor::newBoolean(false) );
				}
			}

//			current( ExpressionConstructor::newBoolean(
//					EVAL_ARG.mARG->at(1).to_ptr< BuiltinCollection >()
//					->contains( EVAL_ARG.mARG->at(0) ) ));

			return( true );
		}
		case AVM_OPCODE_NOTIN:
		{
			BuiltinCollection * aCollection =
					EVAL_ARG.mARG->at(1).to_ptr< BuiltinCollection >();

			if( aCollection->contains( EVAL_ARG.mARG->at(0) ) )
			{
				current( ExpressionConstructor::newBoolean(false) );
			}
			else
			{
				if( aCollection->singleton() )
				{
					current( ExpressionConstructor::neqExpr(
							aCollection->at(0), EVAL_ARG.mARG->at(0)) );
				}
				else if( aCollection->populated() )
				{
					current( ExpressionConstructor::notExpr(
							ExpressionConstructor::newExpr(
								OperatorManager::OPERATOR_CONTAINS,
								EVAL_ARG.mARG->at(1), EVAL_ARG.mARG->at(0)) ));
				}
				else
				{
					current( ExpressionConstructor::newBoolean(true) );
				}
			}

//			current( ExpressionConstructor::newBoolean( not
//					EVAL_ARG.mARG->at(1).to_ptr< BuiltinCollection >()
//					->contains( EVAL_ARG.mARG->at(0) ) ));

			return( true );
		}

		case AVM_OPCODE_INTERSECT:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(0).to_ptr< BuiltinList >()->intersect(
							EVAL_ARG.mARG->at(1).as_ref< BuiltinList >() )));

			return( true );
		}

//		case AVM_OPCODE_STARTS_WITH:
//		{
//			current( ExpressionConstructor::newBoolean( StringTools::startsWith(
//					EVAL_ARG.mARG->at(0).to_ptr< BuiltinCollection >()->getValue(),
//					EVAL_ARG.mARG->at(1).to_ptr< BuiltinCollection >()->getValue() )));
//
//			return( true );
//		}
//		case AVM_OPCODE_ENDS_WITH:
//		{
//			current( ExpressionConstructor::newBoolean( StringTools::endsWith(
//					EVAL_ARG.mARG->at(0).to_ptr< BuiltinCollection >()->getValue(),
//					EVAL_ARG.mARG->at(1).to_ptr< BuiltinCollection >()->getValue() )));
//
//			return( true );
//		}

		case AVM_OPCODE_EMPTY:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(0)
						.to_ptr< BuiltinCollection >()->empty() ) );

			return( true );
		}

		case AVM_OPCODE_NONEMPTY:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(0)
						.to_ptr< BuiltinCollection >()->nonempty() ) );

			return( true );
		}
		case AVM_OPCODE_SINGLETON:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(0)
						.to_ptr< BuiltinCollection >()->singleton() ));

			return( true );
		}
		case AVM_OPCODE_POPULATED:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(0)
						.to_ptr< BuiltinCollection >()->populated()) );

			return( true );
		}
		case AVM_OPCODE_FULL:
		{
			current( ExpressionConstructor::newBoolean(
					EVAL_ARG.mARG->at(0)
						.to_ptr< BuiltinCollection >()->full() ) );

			return( true );
		}

		case AVM_OPCODE_SIZE:
		{
			current( ExpressionConstructor::newUInteger(
					EVAL_ARG.mARG->at(0)
						.to_ptr< BuiltinCollection >()->size() ) );

			return( true );
		}

//		case AVM_OPCODE_EQ:
//		case AVM_OPCODE_SEQ:
//		{
//			current( ExpressionConstructor::newBoolean(
//					EVAL_ARG.mARG->at(0).to_ptr< BuiltinCollection >()->getValue().compare(
//					EVAL_ARG.mARG->at(1).to_ptr< BuiltinCollection >()->getValue()) == 0 ));
//
//			return( true );
//		}
//		case AVM_OPCODE_NEQ:
//		case AVM_OPCODE_NSEQ:
//		{
//			current( ExpressionConstructor::newBoolean(
//					EVAL_ARG.mARG->at(0).to_ptr< BuiltinCollection >()->getValue().compare(
//					EVAL_ARG.mARG->at(1).to_ptr< BuiltinCollection >()->getValue()) != 0 ) );
//
//			return( true );
//		}


		case AVM_OPCODE_TOP:
		{
			current( EVAL_ARG.mARG->at(0).as_ptr< BuiltinQueue >()->top() );

			return( true );
		}

		case AVM_OPCODE_POP:
		{
			current( EVAL_ARG.mARG->at(0).as_ptr< BuiltinQueue >()->pop() );

			return( true );
		}

		case AVM_OPCODE_POP_FROM:
		{
			current( EVAL_ARG.mARG->at(0).as_ptr< BuiltinQueue >()->pop_from(
					EVAL_ARG.mARG->at(1).as_ref< BuiltinList >()) );

			return( true );
		}

		case AVM_OPCODE_PUSH:
		{
			BuiltinContainer * queue =
					EVAL_ARG.mARG->at(0).as_ptr< BuiltinContainer >();
			for( EVAL_ARG.mARG->begin(1) ; EVAL_ARG.mARG->hasNext() ;
					EVAL_ARG.mARG->next() )
			{
				if( not queue->push( EVAL_ARG.mARG->current() ) )
				{
AVM_IF_DEBUG_FLAG( STATEMENT)
	AVM_OS_TRACE << "THROW UNSATISFIED << PUSH >> : "
			<<  outED->mRID.strUniqId() << " |=> "
			<< aCode->str() << std::endl;
	AVM_OS_TRACE << "\t" << "<capacity:" << queue->capacity()
			<< "> " << queue->str() << " <=< "
			<< EVAL_ARG.mARG->current().str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT)

					return( false );
				}
			}

			current( EVAL_ARG.mARG->at(0) );

AVM_IF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )
	AVM_OS_TRACE << "rvalue:> " << queue->str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )

			return( true );
		}

		case AVM_OPCODE_APPEND:
		{
			BuiltinContainer * queue =
					EVAL_ARG.mARG->at(0).to_ptr< BuiltinContainer >();
			for( EVAL_ARG.mARG->begin(1) ; EVAL_ARG.mARG->hasNext() ;
					EVAL_ARG.mARG->next() )
			{
				if( not queue->add( EVAL_ARG.mARG->current() ) )
				{
AVM_IF_DEBUG_FLAG( STATEMENT)
	AVM_OS_TRACE << "THROW UNSATISFIED << APPEND >> : "
			<<  outED->mRID.strUniqId() << " |=> "
			<< aCode->str() << std::endl;
	AVM_OS_TRACE << "\t" << "<capacity:" << queue->capacity()
			<< "> " << queue->str() << " <=< "
			<< EVAL_ARG.mARG->current().str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT)

					return( false );
				}
			}

			current( EVAL_ARG.mARG->at(0) );

AVM_IF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )
			AVM_OS_TRACE << "rvalue:> " << queue->str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )

			return( true );
		}

		case AVM_OPCODE_REMOVE:
		{
			BuiltinContainer * queue =
					EVAL_ARG.mARG->at(0).to_ptr< BuiltinContainer >();
			for( EVAL_ARG.mARG->begin(1) ; EVAL_ARG.mARG->hasNext() ;
					EVAL_ARG.mARG->next() )
			{
				queue->remove( EVAL_ARG.mARG->current() );
			}

			current( EVAL_ARG.mARG->at(0) );

AVM_IF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )
	AVM_OS_TRACE << "rvalue:> " << queue->str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )

			return( true );
		}

		case AVM_OPCODE_ASSIGN_TOP:
		{
			BuiltinQueue * queue = EVAL_ARG.mARG->at(0).to_ptr< BuiltinQueue >();
			if( queue->nonempty() )
			{
AVM_IF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )
	AVM_OS_TRACE << "lvalue:queue> " << queue->str() << std::endl;
	AVM_OS_TRACE << "rvalue:> " << EVAL_ARG.mARG->at(1).str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )

				if( queue->top( EVAL_ARG.mARG->at(1) ) )
				{
AVM_IF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )
	AVM_OS_TRACE << "queue> " << queue->str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )

					current( EVAL_ARG.mARG->at(1) );

					return( true );
				}
				else
				{
AVM_IF_DEBUG_FLAG( STATEMENT)
	AVM_OS_TRACE << "THROW UNSATISFIED << ASSING#TOP >> : "
			<<  outED->mRID.strUniqId() << " |=> "
			<< aCode->str() << std::endl;
	AVM_OS_TRACE << "\t" << "assign#top in queue << "
			<< EVAL_ARG.mARG->at(0).str() << " >> failed !!!"
			<< std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT)

					return( false );
				}
			}
			else
			{
AVM_IF_DEBUG_FLAG( STATEMENT)
	AVM_OS_TRACE << "THROW UNSATISFIED << ASSING#TOP >> : "
			<<  outED->mRID.strUniqId() << " |=> "
			<< aCode->str() << std::endl;
	AVM_OS_TRACE << "\t" << "Unexpected an empty queue << "
			<< EVAL_ARG.mARG->at(0).str() << " >>" << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT)

				return( false );
			}
		}

		case AVM_OPCODE_CTOR:
		{
			BuiltinContainer * containerValue = BuiltinContainer::create(
					EVAL_ARG.mARG->at(0).as_ptr< ContainerTypeSpecifier >() );

			ArrayBF * arrayValue = EVAL_ARG.mARG->at(1).as_ptr< ArrayBF >();

			containerValue->copy( arrayValue, std::min(
					containerValue->capacity(), arrayValue->size()) );

			current( BF( containerValue ) );

			return( true );
		}

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "ARGS_ENV::eval_processor_collection :> "
						"Unexpected bytecode << " << bytecode.strCode()
					<< " >> for : " << aCode->strDebug() << " !!!"
					<< SEND_EXIT;

			return( false );
		}
	}
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// EVAL PROCESSOR BUFFER
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/**
 * EVAL PROCESSOR < AVM_ARG_COLLECTION_CPU >
 */
bool ARGS_ENV::eval_processor_buffer(AvmBytecode & bytecode, BF & arg)
{
	switch( bytecode.operand )
	{
		case AVM_ARG_EXPRESSION_KIND:
		{
			return( eval_processor_buffer(
					bytecode, arg.to_ptr< AvmCode >() ));
		}

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "ARGS_ENV::eval_processor_buffer :> "
						"Unexpected bytecode << " << bytecode.strCode()
					<< " >> for : " << arg.str() << " !!!"
					<< SEND_EXIT;

			current( arg );

			return( false );
		}
	}
}


bool ARGS_ENV::eval_processor_buffer(AvmBytecode & bytecode, AvmCode * aCode)
{
	InstructionEnvironment EVAL_ARG(ENV, outED, aCode->size());
	if( EVAL_ARG.mARG->main_decode_eval_args(aCode) )
	{
		outED = EVAL_ARG.mARG->outED;
	}
	else
	{
		return( aCode );
	}

	switch( aCode->getAvmOpCode() )
	{
//		case AVM_OPCODE_CONTAINS:
//		{
//			current( ExpressionConstructor::newBoolean(
//					EVAL_ARG.mARG->at(0).to_ptr< BaseBufferForm >()
//					->contains( EVAL_ARG.mARG->at(1) ) ));
//
//			return( true );
//		}
//
//		case AVM_OPCODE_IN:
//		{
//			current( ExpressionConstructor::newBoolean(
//					EVAL_ARG.mARG->at(1).to_ptr< BaseBufferForm >()
//					->contains( EVAL_ARG.mARG->at(0) ) ));
//
//			return( true );
//		}
//		case AVM_OPCODE_NOTIN:
//		{
//			current( ExpressionConstructor::newBoolean( not
//					EVAL_ARG.mARG->at(1).to_ptr< BaseBufferForm >()
//					->contains( EVAL_ARG.mARG->at(0) ) ));
//
//			return( true );
//		}
//
////		case AVM_OPCODE_STARTS_WITH:
////		{
////			current( ExpressionConstructor::newBoolean( StringTools::startsWith(
////				EVAL_ARG.mARG->at(0).to_ptr< BaseBufferForm >()->getValue(),
////				EVAL_ARG.mARG->at(1).to_ptr< BaseBufferForm >()->getValue() )));
////
////			return( true );
////		}
////		case AVM_OPCODE_ENDS_WITH:
////		{
////			current( ExpressionConstructor::newBoolean( StringTools::endsWith(
////				EVAL_ARG.mARG->at(0).to_ptr< BaseBufferForm >()->getValue(),
////				EVAL_ARG.mARG->at(1).to_ptr< BaseBufferForm >()->getValue() )));
////
////			return( true );
////		}
//
//		case AVM_OPCODE_EMPTY:
//		{
//			current( ExpressionConstructor::newBoolean(
//					EVAL_ARG.mARG->at(0)
//						.to_ptr< BaseBufferForm >()->empty() ) );
//
//			return( true );
//		}
//
//		case AVM_OPCODE_NONEMPTY:
//		{
//			current( ExpressionConstructor::newBoolean(
//					EVAL_ARG.mARG->at(0)
//						.to_ptr< BaseBufferForm >()->nonempty() ) );
//
//			return( true );
//		}
//		case AVM_OPCODE_SINGLETON:
//		{
//			current( ExpressionConstructor::newBoolean(
//					EVAL_ARG.mARG->at(0)
//						.to_ptr< BaseBufferForm >()->singleton() ) );
//
//			return( true );
//		}
//		case AVM_OPCODE_POPULATED:
//		{
//			current( ExpressionConstructor::newBoolean(
//					EVAL_ARG.mARG->at(0)
//						.to_ptr< BaseBufferForm >()->populated() ) );
//
//			return( true );
//		}
//		case AVM_OPCODE_FULL:
//		{
//			current( ExpressionConstructor::newBoolean(
//					EVAL_ARG.mARG->at(0)
//						.to_ptr< BaseBufferForm >()->full() ) );
//
//			return( true );
//		}
//
//		case AVM_OPCODE_SIZE:
//		{
//			current( ExpressionConstructor::newUInteger(
//					EVAL_ARG.mARG->at(0)
//						.to_ptr< BaseBufferForm >()->size() ) );
//
//			return( true );
//		}
//
////		case AVM_OPCODE_EQ:
////		case AVM_OPCODE_SEQ:
////		{
////			current( ExpressionConstructor::newBoolean(
////				EVAL_ARG.mARG->at(0).to_ptr< BaseBufferForm >()->getValue().compare(
////				EVAL_ARG.mARG->at(1).to_ptr< BaseBufferForm >()->getValue()) == 0 ));
////
////			return( true );
////		}
////		case AVM_OPCODE_NEQ:
////		case AVM_OPCODE_NSEQ:
////		{
////			current( ExpressionConstructor::newBoolean(
////				EVAL_ARG.mARG->at(0).to_ptr< BaseBufferForm >()->getValue().compare(
////				EVAL_ARG.mARG->at(1).to_ptr< BaseBufferForm >()->getValue()) != 0 ) );
////
////			return( true );
////		}
//
//
//		case AVM_OPCODE_TOP:
//		{
//			current( EVAL_ARG.mARG->at(0).to_ptr< BaseBufferForm >()->top() );
//
//			return( true );
//		}
//		case AVM_OPCODE_POP:
//		{
//			current( EVAL_ARG.mARG->at(0).to_ptr< BaseBufferForm >()->pop() );
//
//			return( true );
//		}
//
//		case AVM_OPCODE_PUSH:
//		{
//			BaseBufferForm * queue = EVAL_ARG.mARG->at(0).to_ptr< BaseBufferForm >();
//			for( EVAL_ARG.mARG->begin(1) ; EVAL_ARG.mARG->hasNext() ; EVAL_ARG.mARG->next() )
//			{
//				if( not queue->push( EVAL_ARG.mARG->current() ) )
//				{
//AVM_IF_DEBUG_FLAG( STATEMENT)
//	AVM_OS_TRACE << "THROW UNSATISFIED << PUSH >> : "
//			<<  outED->mRID.strUniqId() << " |=> "
//			<< aCode->str() << std::endl;
//	AVM_OS_TRACE << "\t" << "<capacity:" << queue->capacity()
//			<< "> " << queue->str() << " <=< "
//			<< EVAL_ARG.mARG->current().str() << std::endl;
//AVM_ENDIF_DEBUG_FLAG( STATEMENT)
//
//					return( false );
//				}
//			}
//AVM_IF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )
//	AVM_OS_TRACE << "rvalue:> " << queue->str() << std::endl;
//AVM_ENDIF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )
//
//			return( true );
//		}
//
//		case AVM_OPCODE_APPEND:
//		{
//			BaseBufferForm * queue = EVAL_ARG.mARG->at(0).to_ptr< BaseBufferForm >();
//			for( EVAL_ARG.mARG->begin(1) ; EVAL_ARG.mARG->hasNext() ; EVAL_ARG.mARG->next() )
//			{
//				if( not queue->append( EVAL_ARG.mARG->current() ) )
//				{
//AVM_IF_DEBUG_FLAG( STATEMENT)
//	AVM_OS_TRACE << "THROW UNSATISFIED << APPEND >> : "
//			<<  outED->mRID.strUniqId() << " |=> "
//			<< aCode->str() << std::endl;
//	AVM_OS_TRACE << "\t" << "<capacity:" << queue->capacity()
//			<< "> " << queue->str() << " <=< "
//			<< EVAL_ARG.mARG->current().str() << std::endl;
//AVM_ENDIF_DEBUG_FLAG( STATEMENT)
//
//					return( false );
//				}
//			}
//AVM_IF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )
//	AVM_OS_TRACE << "rvalue:> " << queue->str() << std::endl;
//AVM_ENDIF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )
//
//			return( true );
//		}

		case AVM_OPCODE_REMOVE:
		{
			BaseBufferForm * bbf = EVAL_ARG.mARG->at(0).to_ptr< BaseBufferForm >();
			if( EVAL_ARG.mARG->at(1).is< InstanceOfPort >() )
			{
				bbf->remove( EVAL_ARG.mARG->at(1).to_ptr< InstanceOfPort >() );

AVM_IF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )
			AVM_OS_TRACE << "rvalue:> " << bbf->str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )

				return( true );
			}

			return( false );
		}

//		case AVM_OPCODE_ASSIGN_TOP:
//		{
//			BaseBufferForm * queue = EVAL_ARG.mARG->at(0).to_ptr< BaseBufferForm >();
//			if( queue->nonempty() )
//			{
//AVM_IF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )
//	AVM_OS_TRACE << "lvalue:queue> " << queue->str() << std::endl;
//	AVM_OS_TRACE << "rvalue:> " << EVAL_ARG.mARG->at(1).str() << std::endl;
//AVM_ENDIF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )
//
//				if( queue->top( EVAL_ARG.mARG->at(1) ) )
//				{
//AVM_IF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )
//	AVM_OS_TRACE << "queue> " << queue->str() << std::endl;
//AVM_ENDIF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )
//
//					current( EVAL_ARG.mARG->at(1) );
//
//					return( true );
//				}
//				else
//				{
//AVM_IF_DEBUG_FLAG( STATEMENT)
//	AVM_OS_TRACE << "THROW UNSATISFIED << ASSING#TOP >> : "
//			<<  outED->mRID.strUniqId() << " |=> "
//			<< aCode->str() << std::endl;
//	AVM_OS_TRACE << "\t" << "assign#top in queue << "
//			<< EVAL_ARG.mARG->at(0).str() << " >> failed !!!"
//			<< std::endl;
//AVM_ENDIF_DEBUG_FLAG( STATEMENT)
//
//					return( false );
//				}
//			}
//			else
//			{
//AVM_IF_DEBUG_FLAG( STATEMENT)
//	AVM_OS_TRACE << "THROW UNSATISFIED << ASSING#TOP >> : "
//			<<  outED->mRID.strUniqId() << " |=> "
//			<< aCode->str() << std::endl;
//	AVM_OS_TRACE << "\t" << "Unexpected an empty queue << "
//			<< EVAL_ARG.mARG->at(0).str() << " >>" << std::endl;
//AVM_ENDIF_DEBUG_FLAG( STATEMENT)
//
//				return( false );
//			}
//		}

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "ARGS_ENV::eval_processor_collection :> "
						"Unexpected bytecode << " << bytecode.strCode()
					<< " >> for : " << aCode->strDebug() << " !!!"
					<< SEND_EXIT;

			return( false );
		}
	}
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/**
 * Serialization
 */
void ARGS_ENV::argsStream(OutStream & os)
{
	begin();

	if( hasNext() )
	{
		os << TAB << "$[" << EOL_TAB2 << current().str();

		for( next() ; hasNext() ; next() )
		{
			os << " ," << EOL_TAB2 << current().str();
		}

		os << EOL_TAB << "]" << EOL_FLUSH;
	}
}



} /* namespace sep */
