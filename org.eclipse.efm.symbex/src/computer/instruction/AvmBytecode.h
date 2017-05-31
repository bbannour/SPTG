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

#ifndef AVMBYTECODE_H_
#define AVMBYTECODE_H_

#include <printer/OutStream.h>

#include <util/avm_numeric.h>


namespace sep
{

/**
 * Evaluation context
 */
enum AVM_ARG_CONTEXT
{
	AVM_ARG_UNDEFINED_CONTEXT = 0x0000,

	AVM_ARG_STANDARD_CTX,

	AVM_ARG_ARGUMENT_CTX,

	AVM_ARG_PARAMETER_CTX,

	AVM_ARG_RETURN_CTX,

};

//typedef avm_uint8_t         avm_arg_context_t;
typedef AVM_ARG_CONTEXT       avm_arg_context_t;


/**
 * Evaluation co-processor unit (CPU)
 */
enum AVM_ARG_PROCESSOR
{
	AVM_ARG_UNDEFINED_PROCESSOR = 0x0000,

	AVM_ARG_NOP_CPU,
	AVM_ARG_NOPS_CPU,

	AVM_ARG_MEMORY_LVALUE_CPU,
	AVM_ARG_MEMORY_WVALUE_CPU,
	AVM_ARG_MEMORY_RVALUE_CPU,
	AVM_ARG_MEMORY_MACHINE_CPU,

	AVM_ARG_ARITHMETIC_LOGIC_CPU,

	AVM_ARG_CHARACTER_CPU,

	AVM_ARG_STRING_CPU,

	AVM_ARG_ARRAY_LVALUE_CPU,
	AVM_ARG_ARRAY_RVALUE_CPU,

	AVM_ARG_VECTOR_CPU,

	AVM_ARG_QUEUE_CPU,
	AVM_ARG_LIST_CPU,
	AVM_ARG_COLLECTION_CPU,

	AVM_ARG_BUFFER_CPU,

	AVM_ARG_STATEMENT_CPU,

};

//typedef avm_uint8_t         avm_arg_processor_t;
typedef AVM_ARG_PROCESSOR     avm_arg_processor_t;


/**
 * Evaluation operation
 */
enum AVM_ARG_OPERATION
{
	AVM_ARG_UNDEFINED_OPERATION = 0x0000,

	// 4 bits :> PREFIX  CODE
	// : 0001:nop
	// : 0011:nops
	AVM_ARG_NOP                 = 0x0001,

	AVM_ARG_NOP_ALL             = 0x0002,
	AVM_ARG_NOPS                = AVM_ARG_NOP_ALL | AVM_ARG_NOP,
	// : 0100:sroutine_eval
	// : 1000:mroutine_eval
	AVM_ARG_SEVAL               = 0x0004,
	AVM_ARG_MEVAL               = 0x0008,

	// 4 bits :> LR-VALUE  CODE
	// | 0001:lvalue
	// | 0010:rvalue
	// | 0100:wvalue
	// | 1000:lr_value
	AVM_ARG_LVALUE              = 0x0010,
	AVM_ARG_WVALUE              = 0x0020,
	AVM_ARG_RVALUE              = 0x0040,

	AVM_ARG_VALUE               = AVM_ARG_LVALUE
	                            | AVM_ARG_WVALUE
	                            | AVM_ARG_RVALUE,


	// Combinaison [S|M]EVAL with VALUE
	AVM_ARG_SEVAL_LVALUE        = AVM_ARG_SEVAL | AVM_ARG_LVALUE,
	AVM_ARG_SEVAL_WVALUE        = AVM_ARG_SEVAL | AVM_ARG_WVALUE,
	AVM_ARG_SEVAL_RVALUE        = AVM_ARG_SEVAL | AVM_ARG_RVALUE,

	AVM_ARG_SEVAL_VALUE         = AVM_ARG_SEVAL | AVM_ARG_VALUE,

	AVM_ARG_MEVAL_LVALUE        = AVM_ARG_MEVAL | AVM_ARG_LVALUE,
	AVM_ARG_MEVAL_WVALUE        = AVM_ARG_MEVAL | AVM_ARG_WVALUE,
	AVM_ARG_MEVAL_RVALUE        = AVM_ARG_MEVAL | AVM_ARG_RVALUE,

	AVM_ARG_MEVAL_VALUE         = AVM_ARG_MEVAL | AVM_ARG_VALUE,

	// Combinaison NOP with [S|M]EVAL with VALUE
	AVM_ARG_NOP_LVALUE          = AVM_ARG_NOP  | AVM_ARG_LVALUE,
	AVM_ARG_NOP_RVALUE          = AVM_ARG_NOP  | AVM_ARG_RVALUE,

	AVM_ARG_NOP_VALUE           = AVM_ARG_NOP  | AVM_ARG_VALUE,

	// Combinaison NOPS with [S|M]EVAL with VALUE
	AVM_ARG_NOPS_LVALUE         = AVM_ARG_NOPS | AVM_ARG_LVALUE,
	AVM_ARG_NOPS_RVALUE         = AVM_ARG_NOPS | AVM_ARG_RVALUE,

	AVM_ARG_NOPS_VALUE          = AVM_ARG_NOPS | AVM_ARG_VALUE,

};

//typedef avm_uint8_t           avm_arg_operation_t;
typedef AVM_ARG_OPERATION       avm_arg_operation_t;


#define AVM_ARG_OPERATION_NOP_MASK     (AVM_ARG_NOP | AVM_ARG_NOPS)

#define IS_ARG_OPERATION_NOP(op)       (op & AVM_ARG_NOP)
#define IS_ARG_OPERATION_NOPS(op)      (op & AVM_ARG_NOP_ALL)


#define AVM_ARG_OPERATION_EVAL_MASK    (AVM_ARG_SEVAL | AVM_ARG_MEVAL)

#define IS_ARG_OPERATION_EVAL(op)      ((op & AVM_ARG_NOP) == 0)
#define IS_ARG_OPERATION_SEVAL(op)     (IS_ARG_OPERATION_EVAL(op) && (op & AVM_ARG_SEVAL) )
#define IS_ARG_OPERATION_MEVAL(op)     (IS_ARG_OPERATION_EVAL(op) && (op & AVM_ARG_MEVAL) )


#define AVM_ARG_OPERATION_PREFIX_MASK  (AVM_ARG_OPERATION_NOP_MASK | AVM_ARG_OPERATION_EVAL_MASK)

#define HAS_ARG_OPERATION_PREFIX(op)   ((op & AVM_ARG_OPERATION_PREFIX_MASK) != 0)


#define AVM_ARG_OPERATION_X_SEVAL_MASK (AVM_ARG_SEVAL | (~ AVM_ARG_OPERATION_PREFIX_MASK))
#define AVM_ARG_OPERATION_X_MEVAL_MASK (AVM_ARG_MEVAL | (~ AVM_ARG_OPERATION_PREFIX_MASK))


#define AVM_ARG_OPERATION_VALUE_MASK   ( AVM_ARG_LVALUE  | AVM_ARG_WVALUE  | AVM_ARG_RVALUE )


/**
 * Evaluation operand
 */
enum AVM_ARG_OPERAND
{
	AVM_ARG_UNDEFINED_OPERAND = 0x0000,

	// 4 bit :> argument kind
	// | 0001:data
	// | 0011:data#ref
	// | 0101:data#macro
	// | 0100:expression
	// : 1000:builtin
	AVM_ARG_DATA_KIND,
	AVM_ARG_DATA_CST_KIND,
	AVM_ARG_DATA_REF_KIND,
	AVM_ARG_DATA_MACRO_KIND,
	AVM_ARG_DATA_UFI_KIND,

	AVM_ARG_PORT_KIND,
	AVM_ARG_BUFFER_KIND,
	AVM_ARG_CONNECTOR_KIND,

	AVM_ARG_BUILTIN_KIND,
	AVM_ARG_BUILTIN_ARRAY_KIND,
	AVM_ARG_BUILTIN_CONTAINER_KIND,

	AVM_ARG_BOOLEAN_KIND,

	AVM_ARG_INTEGER_KIND,
	AVM_ARG_RATIONAL_KIND,
	AVM_ARG_FLOAT_KIND,

	AVM_ARG_CHARACTER_KIND,
	AVM_ARG_STRING_KIND,

	AVM_ARG_ARRAY_KIND,
	AVM_ARG_COLLECTION_KIND,

	AVM_ARG_MACHINE_RID,
	AVM_ARG_EXPRESSION_RID,

	AVM_ARG_SELF_RID,
	AVM_ARG_PARENT_RID,
	AVM_ARG_COMMUNICATOR_RID,
	AVM_ARG_SYSTEM_RID,
	AVM_ARG_ENVIRONMENT_RID,

	AVM_ARG_COMPONENT_SELF_RID,
	AVM_ARG_COMPONENT_PARENT_RID,
	AVM_ARG_COMPONENT_COMMUNICATOR_RID,

	AVM_ARG_OPERATOR_KIND,

	AVM_ARG_EXPRESSION_KIND,

	AVM_ARG_STATEMENT_KIND,

	AVM_ARG_CTOR_TYPE_KIND,

};

//typedef avm_uint8_t           avm_arg_operand_t;
typedef AVM_ARG_OPERAND         avm_arg_operand_t;


/**
 * Avm bytecode definition
 */

class ARGS_ENV;
class AvmCode;
class BaseTypeSpecifier;
class BF;


struct AvmBytecode
{

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmBytecode(avm_arg_context_t aContext, avm_arg_processor_t aProcessor,
			avm_arg_operation_t anOperation, avm_arg_operand_t anOperand,
			BaseTypeSpecifier * aType);

	AvmBytecode(avm_arg_context_t aContext, avm_arg_processor_t aProcessor,
			avm_arg_operation_t anOperation = AVM_ARG_UNDEFINED_OPERATION,
			avm_arg_operand_t anOperand = AVM_ARG_UNDEFINED_OPERAND);

	AvmBytecode(avm_arg_context_t aContext,
			avm_arg_operation_t anOperation = AVM_ARG_UNDEFINED_OPERATION,
			avm_arg_operand_t anOperand = AVM_ARG_UNDEFINED_OPERAND);

	AvmBytecode(avm_arg_operation_t anOperation = AVM_ARG_UNDEFINED_OPERATION,
			avm_arg_operand_t anOperand = AVM_ARG_UNDEFINED_OPERAND);


//	/**
//	 * CONSTRUCTOR
//	 * Copy
//	 */
//	AvmBytecode(const AvmBytecode & aBytecode)
//	: context( aBytecode.context ),
//	processor( aBytecode.processor ),
//	numeric( aBytecode.numeric ),
//	operation( aBytecode.operation ),
//	operand( aBytecode.operand ),
//	offset( aBytecode.offset ),
//	dtype( aBytecode.dtype ),
//
//	routine_decode_eval( aBytecode.routine_decode_eval ),
//	routine_eval( aBytecode.routine_eval ),
//	routine_decode_run( aBytecode.routine_decode_run ),
//	routine_run( aBytecode.routine_run )
//	{
//		//!! NOTHING
//	}


	/**
	 * operation
	 * operand
	 * result
	 */
	void set(avm_arg_context_t aContext,
			avm_arg_processor_t aProcessor, avm_arg_operation_t anOperation,
			avm_arg_operand_t anOperand, BaseTypeSpecifier * aType = NULL)
	{
		context   = aContext;
		processor = aProcessor;
		operation = anOperation;
		operand   = anOperand;
		dtype     = aType;
	}


	void set(avm_arg_operation_t anOperation, avm_arg_operand_t anOperand)
	{
		operation = anOperation;
		operand   = anOperand;
	}


	/**
	 * dtype
	 */
	bool hasType() const;

	/**
	 * NOP
	 * NOPS
	 * EVALS
	 */
	inline bool isNopCpu() const
	{
		return( (processor == AVM_ARG_NOP_CPU) ||
				(processor == AVM_ARG_NOPS_CPU) );
	}

	inline void setNopCpu(
			avm_arg_operation_t opMask = AVM_ARG_UNDEFINED_OPERATION)
	{
		processor = AVM_ARG_NOP_CPU;

		operation = avm_arg_operation_t(operation | opMask | AVM_ARG_NOP);

		operation = avm_arg_operation_t(operation &
				(~AVM_ARG_OPERATION_EVAL_MASK));
	}


	inline bool isNopOperation() const
	{
		return( IS_ARG_OPERATION_NOP(operation) );
	}

	inline void setNopOperation(
			avm_arg_operation_t opMask = AVM_ARG_UNDEFINED_OPERATION)
	{
		operation = avm_arg_operation_t(operation | opMask | AVM_ARG_NOP);

		operation = avm_arg_operation_t(operation &
				(~AVM_ARG_OPERATION_EVAL_MASK));
	}


	inline bool isNopsOperation() const
	{
		return( IS_ARG_OPERATION_NOPS(operation) );
	}

	inline void setNopsOperation(
			avm_arg_operation_t opMask = AVM_ARG_UNDEFINED_OPERATION)
	{
		operation = avm_arg_operation_t(operation | opMask | AVM_ARG_NOPS);

		operation = avm_arg_operation_t( operation &
				(~AVM_ARG_OPERATION_EVAL_MASK));
	}

	inline void unsetNopsOperation(avm_arg_operation_t opMask = AVM_ARG_SEVAL)
	{
		operation = avm_arg_operation_t( (operation | opMask) &
				(~ AVM_ARG_OPERATION_NOP_MASK));
	}


	inline bool isEval() const
	{
		return( IS_ARG_OPERATION_EVAL(operation) );
	}

	inline void unsetEval()
	{
		operation = avm_arg_operation_t( operation &
				(~ AVM_ARG_OPERATION_EVAL_MASK) );
	}


	inline bool isSeval() const
	{
		return( IS_ARG_OPERATION_SEVAL(operation) );
	}

	inline void setSeval(avm_arg_operation_t opMask = AVM_ARG_UNDEFINED_OPERATION)
	{
		operation = avm_arg_operation_t(operation | opMask | AVM_ARG_SEVAL);
	}

	// eXclusive PREFIX bit setting
	inline void xsetSeval(avm_arg_operation_t opMask = AVM_ARG_UNDEFINED_OPERATION)
	{
		operation = avm_arg_operation_t( (operation | opMask) &
				AVM_ARG_OPERATION_X_SEVAL_MASK );
	}

	inline void unsetSeval()
	{
		operation = avm_arg_operation_t( operation & (~ AVM_ARG_SEVAL) );
	}


	inline bool isMeval() const
	{
		return( IS_ARG_OPERATION_MEVAL(operation) );
	}

	inline void setMeval(avm_arg_operation_t opMask = AVM_ARG_UNDEFINED_OPERATION)
	{
		operation = avm_arg_operation_t(operation | opMask | AVM_ARG_MEVAL);
	}

	// eXclusive PREFIX bit setting
	inline void xsetMeval(avm_arg_operation_t opMask = AVM_ARG_UNDEFINED_OPERATION)
	{
		operation = avm_arg_operation_t( (operation | opMask) &
				AVM_ARG_OPERATION_X_MEVAL_MASK );
	}

	inline void unsetMeval()
	{
		operation = avm_arg_operation_t( operation & (~ AVM_ARG_MEVAL) );
	}


	static AvmBytecode ARG_UNDEFINED_CODE;

	static AvmBytecode ARG_NOPS_CODE;
	static AvmBytecode ARG_SEVAL_CODE;
	static AvmBytecode ARG_MEVAL_CODE;


	/**
	 * COMPARISON
	 * OPERATOR
	 */

	inline bool operator==(const AvmBytecode & other) const
	{
		return( (context   == other.context  ) &&
				(processor == other.processor) &&
				(numeric   == other.numeric  ) &&
				(operation == other.operation) &&
				(operand   == other.operand  ) &&
				(offset    == other.offset   ) &&
				(dtype     == other.dtype)   );
	}


	/**
	 * Serialization
	 */
	static std::string strContext(avm_arg_context_t context);

	static std::string strProcessor(avm_arg_processor_t processor);


	static std::string strNopCode(avm_arg_operation_t operation);

	static std::string strEvalCode(avm_arg_operation_t operation);

	inline static std::string strPrefixCode(avm_arg_operation_t operation)
	{
		if( HAS_ARG_OPERATION_PREFIX(operation) )
		{
			std::string nop  = strNopCode(operation);
			std::string routine_eval = strEvalCode(operation);

			return( nop.empty() ? routine_eval :
					(routine_eval.empty() ? nop :
							(OSS() << nop << "#" << routine_eval).str()) );
		}
		else
		{
			return( "?routine_eval" );
		}
	}


	static std::string strValueCode(avm_arg_operation_t operation);

	inline static std::string strOperation(avm_arg_operation_t operation)
	{
		return( OSS() << strPrefixCode(operation) << ":"
				<< strValueCode(operation) );
	}


	static std::string strOperand(avm_arg_operand_t operand);


	inline static std::string strCode(
			avm_arg_context_t context, avm_arg_processor_t processor,
			avm_arg_operation_t operation, avm_arg_operand_t operand)
	{
		std::ostringstream oss;

		oss << strContext(context) << "[" << strProcessor(processor) << "]:>"
			<< strOperation(operation) << ":" << strOperand(operand);

		return( oss.str() );
	}


	inline std::string strPrefixCode() const
	{
		return( AvmBytecode::strPrefixCode(operation) );
	}

	inline std::string strValueCode() const
	{
		return( AvmBytecode::strValueCode(operation) );
	}

	inline std::string strExpressionCode() const
	{
		return( AvmBytecode::strOperand(operand) );
	}

	inline std::string strCode() const
	{
		std::ostringstream oss;

		oss << AvmBytecode::strCode(context, processor, operation, operand);
		if( offset != AVM_NUMERIC_MAX_SIZE_T )
		{
			oss << "<<" << offset;
		}

		return( oss.str() );
	}

	std::string strType() const;


	/*
	 * ATTRIBUTES
	 */
	// context
	avm_arg_context_t context;

	// routine_evaluation processor
	avm_arg_processor_t processor;

	// is numeric valuation flag
	bool numeric;

	// operation
	avm_arg_operation_t operation;

	// operand<nature> used by the operation
	avm_arg_operand_t operand;

	// offset of operand in input table
	avm_size_t offset;

	// type of operand
	BaseTypeSpecifier * dtype;


	////////////////////////////////////////////////////////////////////////////
	// optimize API for << [decode] eval >> routine
	////////////////////////////////////////////////////////////////////////////

	bool (* routine_decode_eval)(AvmBytecode *, ARGS_ENV &, const BF &);

	inline bool decode_eval(ARGS_ENV & argENV, const BF & arg)
	{
		return( routine_decode_eval(this, argENV, arg) );
	}


	bool (* routine_eval)(AvmBytecode *, ARGS_ENV &, AvmCode *);

	inline bool eval(ARGS_ENV & argENV, AvmCode * aCode)
	{
		return( routine_eval(this, argENV, aCode) );
	}


	////////////////////////////////////////////////////////////////////////////
	// optimize API for << [decode] run >> routine
	////////////////////////////////////////////////////////////////////////////

	bool (* routine_decode_run)(AvmBytecode *, ARGS_ENV &, const BF &);

	inline bool decode_run(ARGS_ENV & argENV, const BF & arg)
	{
		return( routine_decode_run(this, argENV, arg) );
	}


	bool (* routine_run)(AvmBytecode *, ARGS_ENV &, AvmCode *);

	inline bool run(ARGS_ENV & argENV, AvmCode * aCode)
	{
		return( routine_run(this, argENV, aCode) );
	}


};


} /* namespace sep */
#endif /* AVMBYTECODE_H_ */
