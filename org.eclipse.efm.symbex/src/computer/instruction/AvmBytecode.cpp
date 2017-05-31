/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 1 mars 2013
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmBytecode.h"

#include <common/BF.h>

#include <fml/executable/ExecutableLib.h>
#include <fml/executable/InstanceOfData.h>

#include <fml/type/BaseTypeSpecifier.h>
#include <fml/type/TypeManager.h>


namespace sep
{


AvmBytecode AvmBytecode::ARG_UNDEFINED_CODE(
		/*context  */ AVM_ARG_UNDEFINED_CONTEXT,
		/*processor*/ AVM_ARG_UNDEFINED_PROCESSOR,
		/*operation*/ AVM_ARG_UNDEFINED_OPERATION,
		/*operand  */ AVM_ARG_UNDEFINED_OPERAND,
		/*dtype    */ NULL);


AvmBytecode AvmBytecode::ARG_NOPS_CODE(AVM_ARG_NOPS);

AvmBytecode AvmBytecode::ARG_SEVAL_CODE(AVM_ARG_SEVAL);

AvmBytecode AvmBytecode::ARG_MEVAL_CODE(AVM_ARG_MEVAL);


/**
 * CONSTRUCTOR
 * Default
 */
AvmBytecode::AvmBytecode(
		avm_arg_context_t aContext, avm_arg_processor_t aProcessor,
		avm_arg_operation_t anOperation, avm_arg_operand_t anOperand,
		BaseTypeSpecifier * aType)
: context( aContext ),
processor( aProcessor ),
numeric( false ),
operation( anOperation ),
operand( anOperand ),
offset( AVM_NUMERIC_MAX_SIZE_T ),
dtype( aType ),

routine_decode_eval( NULL ),
routine_eval( NULL ),
routine_decode_run( NULL ),
routine_run( NULL )
{
	//!!  NOTHING
}

AvmBytecode::AvmBytecode(
		avm_arg_context_t aContext, avm_arg_processor_t aProcessor,
		avm_arg_operation_t anOperation, avm_arg_operand_t anOperand)
: context( aContext ),
processor( aProcessor ),
numeric( false ),
operation( anOperation ),
operand( anOperand ),
offset( AVM_NUMERIC_MAX_SIZE_T ),
dtype( TypeManager::UNIVERSAL ),

routine_decode_eval( NULL ),
routine_eval( NULL ),
routine_decode_run( NULL ),
routine_run( NULL )
{
	//!!  NOTHING
}

AvmBytecode::AvmBytecode( avm_arg_context_t aContext,
		avm_arg_operation_t anOperation, avm_arg_operand_t anOperand)
: context( aContext ),
processor( AVM_ARG_UNDEFINED_PROCESSOR ),
numeric( false ),
operation( anOperation ),
operand( anOperand ),
offset( AVM_NUMERIC_MAX_SIZE_T ),
dtype( TypeManager::UNIVERSAL ),

routine_decode_eval( NULL ),
routine_eval( NULL ),
routine_decode_run( NULL ),
routine_run( NULL )
{
	//!!  NOTHING
}

AvmBytecode::AvmBytecode(
		avm_arg_operation_t anOperation, avm_arg_operand_t anOperand)
: context( AVM_ARG_STANDARD_CTX ),
processor( AVM_ARG_UNDEFINED_PROCESSOR ),
numeric( false ),
operation( anOperation ),
operand( anOperand ),
offset( AVM_NUMERIC_MAX_SIZE_T ),
dtype( TypeManager::UNIVERSAL ),

routine_decode_eval( NULL ),
routine_eval( NULL ),
routine_decode_run( NULL ),
routine_run( NULL )
{
	//!!  NOTHING
}


/**
 * dtype
 */
bool AvmBytecode::hasType() const
{
	return( (dtype != NULL) && (dtype != TypeManager::UNIVERSAL) );
}


/**
 * Serialization
 */
std::string AvmBytecode::strContext(avm_arg_context_t context)
{
	switch( context )
	{
		case AVM_ARG_STANDARD_CTX:
		{
			return( "std" );
		}

		case AVM_ARG_ARGUMENT_CTX:
		{
			return( "arg" );
		}

		case AVM_ARG_PARAMETER_CTX:
		{
			return( "param" );
		}

		case AVM_ARG_RETURN_CTX:
		{
			return( "ret" );
		}

		case AVM_ARG_UNDEFINED_CONTEXT:
		default:
		{
			return( "?ctx" );
		}
	}
}


std::string AvmBytecode::strProcessor(avm_arg_processor_t processor)
{
	switch( processor )
	{
		case AVM_ARG_NOP_CPU:
		{
			return( "nop" );
		}
		case AVM_ARG_NOPS_CPU:
		{
			return( "nops" );
		}

		case AVM_ARG_MEMORY_LVALUE_CPU:
		{
			return( "dma:lv" );
		}
		case AVM_ARG_MEMORY_WVALUE_CPU:
		{
			return( "dma:wv" );
		}
		case AVM_ARG_MEMORY_RVALUE_CPU:
		{
			return( "dma:rv" );
		}
		case AVM_ARG_MEMORY_MACHINE_CPU:
		{
			return( "dma:rid" );
		}

		case AVM_ARG_ARITHMETIC_LOGIC_CPU:
		{
			return( "alu" );
		}

		case AVM_ARG_CHARACTER_CPU:
		{
			return( "char" );
		}
		case AVM_ARG_STRING_CPU:
		{
			return( "string" );
		}

		case AVM_ARG_ARRAY_LVALUE_CPU:
		{
			return( "array:lv" );
		}
		case AVM_ARG_ARRAY_RVALUE_CPU:
		{
			return( "array:rv" );
		}

		case AVM_ARG_VECTOR_CPU:
		{
			return( "vector" );
		}

		case AVM_ARG_QUEUE_CPU:
		{
			return( "queue" );
		}
		case AVM_ARG_LIST_CPU:
		{
			return( "list" );
		}
		case AVM_ARG_COLLECTION_CPU:
		{
			return( "collection" );
		}

		case AVM_ARG_BUFFER_CPU:
		{
			return( "buffer" );
		}

		case AVM_ARG_STATEMENT_CPU:
		{
			return( "stm" );
		}

		case AVM_ARG_UNDEFINED_PROCESSOR:
		default:
		{
			return( "?processor" );
		}
	}
}


std::string AvmBytecode::strNopCode(avm_arg_operation_t operation)
{
	switch( operation & AVM_ARG_OPERATION_NOP_MASK )
	{
		case AVM_ARG_NOP:
		{
			return( "nop" );
		}
		case AVM_ARG_NOPS:
		{
			return( "nops" );
		}

		default:
		{
			return( "" );
		}
	}
}

std::string AvmBytecode::strEvalCode(avm_arg_operation_t operation)
{
	switch( operation & AVM_ARG_OPERATION_EVAL_MASK )
	{
		case AVM_ARG_SEVAL:
		{
			return( "seval" );
		}

		case AVM_ARG_MEVAL:
		{
			return( "meval" );
		}

		default:
		{
			return( "" );
		}
	}
}


std::string AvmBytecode::strValueCode(avm_arg_operation_t operation)
{
	switch( operation & AVM_ARG_OPERATION_VALUE_MASK )
	{
		case AVM_ARG_RVALUE:
		{
			return( "rvalue" );
		}
		case AVM_ARG_LVALUE:
		{
			return( "lvalue" );
		}
		case AVM_ARG_WVALUE:
		{
			return( "wvalue" );
		}

		case AVM_ARG_VALUE:
		{
			return( "value" );
		}

		default:
		{
			return( "?value" );
		}
	}
}


std::string AvmBytecode::strOperand(avm_arg_operand_t operand)
{
	switch( operand )
	{
		case AVM_ARG_DATA_KIND:
		{
			return( "data" );
		}
		case AVM_ARG_DATA_CST_KIND:
		{
			return( "const" );
		}
		case AVM_ARG_DATA_REF_KIND:
		{
			return( "ref" );
		}
		case AVM_ARG_DATA_MACRO_KIND:
		{
			return( "macro" );
		}
		case AVM_ARG_DATA_UFI_KIND:
		{
			return( "ufi" );
		}

		case AVM_ARG_PORT_KIND:
		{
			return( "port" );
		}
		case AVM_ARG_BUFFER_KIND:
		{
			return( "buffer" );
		}
		case AVM_ARG_CONNECTOR_KIND:
		{
			return( "connector" );
		}

		case AVM_ARG_BUILTIN_KIND:
		{
			return( "builtin" );
		}
		case AVM_ARG_BUILTIN_ARRAY_KIND:
		{
			return( "built#array" );
		}
		case AVM_ARG_BUILTIN_CONTAINER_KIND:
		{
			return( "built#collection" );
		}

		case AVM_ARG_BOOLEAN_KIND:
		{
			return( "boolean" );
		}
		case AVM_ARG_INTEGER_KIND:
		{
			return( "integer" );
		}
		case AVM_ARG_RATIONAL_KIND:
		{
			return( "rational" );
		}
		case AVM_ARG_FLOAT_KIND:
		{
			return( "float" );
		}
		case AVM_ARG_CHARACTER_KIND:
		{
			return( "char" );
		}
		case AVM_ARG_STRING_KIND:
		{
			return( "string" );
		}

		case AVM_ARG_OPERATOR_KIND:
		{
			return( "operator" );
		}

		case AVM_ARG_EXPRESSION_KIND:
		{
			return( "expression" );
		}
		case AVM_ARG_ARRAY_KIND:
		{
			return( "array" );
		}
		case AVM_ARG_COLLECTION_KIND:
		{
			return( "collection" );
		}

		case AVM_ARG_STATEMENT_KIND:
		{
			return( "statement" );
		}

		case AVM_ARG_CTOR_TYPE_KIND:
		{
			return( "ctor#type" );
		}


		case AVM_ARG_MACHINE_RID:
		{
			return( "machine#rid" );
		}

		case AVM_ARG_EXPRESSION_RID:
		{
			return( "expr#rid" );
		}

		case AVM_ARG_SELF_RID:
		{
			return( "self#rid" );
		}
		case AVM_ARG_PARENT_RID:
		{
			return( "parent#rid" );
		}
		case AVM_ARG_COMMUNICATOR_RID:
		{
			return( "com#rid" );
		}
		case AVM_ARG_SYSTEM_RID:
		{
			return( "system#rid" );
		}
		case AVM_ARG_ENVIRONMENT_RID:
		{
			return( "env#rid" );
		}
		case AVM_ARG_COMPONENT_SELF_RID:
		{
			return( "component#self#rid" );
		}
		case AVM_ARG_COMPONENT_PARENT_RID:
		{
			return( "component#parent#rid" );
		}
		case AVM_ARG_COMPONENT_COMMUNICATOR_RID:
		{
			return( "component#com#rid" );
		}

		default:
		{
			return( "?expression" );
		}
	}
}


std::string AvmBytecode::strType() const
{
	return( (dtype != NULL) ? dtype->strT() : "null<dtype>" );
}



} /* namespace sep */
