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

#ifndef INSTRUCTIONENVIRONMENT_H_
#define INSTRUCTIONENVIRONMENT_H_

#include <common/AvmObject.h>
#include <common/BF.h>

#include <collection/List.h>
#include <collection/Vector.h>

#include <fml/runtime/ExecutionData.h>


#define ARGS_ENV_INITIAL_CACHE_COUNT     32

#define ARGS_ENV_DEFAULT_CAPACITY        16

#define ARGS_ENV_INCR_CAPACITY           8



namespace sep
{

class AvmCode;
class ArrayBF;
class BaseEnvironment;
class ContainerTypeSpecifier;


struct ARGS_ENV
{
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ARGS_ENV(BaseEnvironment * aENV,
			const APExecutionData & outED,
			avm_size_t aCapacity, avm_size_t aCount)
	: NEXT( NULL ),
	ENV( aENV ),
	outED( outED ),
	table( aCount ),
	values( & table ),

	argsInstruction( NULL ),
	argsBytecode( NULL ),

	capacity( aCapacity ),
	count( aCount ),
	idx( 0 )
	{
		table.reserve( aCapacity );

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
	AVM_OS_TRACE << "new ARGS_ENV :>"
			<< " capacity = " << std::setw(4) << capacity
			<< " : count = " << std::setw(4) << count
			<< " @" << avm_address_t( this ) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~ARGS_ENV()
	{
		values = NULL;
		table.clear();
		capacity = count = idx = 0;
	}


	/**
	 * EMPTYNESS
	 */
	inline bool empty() const
	{
		return( count == 0 );
	}

	inline bool nonempty() const
	{
		return( count > 0 );
	}


	/**
	 * ITERATOR
	 */
	inline void begin(avm_size_t offset = 0)
	{
		idx = offset;
	}

	inline bool hasNext() const
	{
		return( idx < count );
	}

	inline BF & current()
	{
		return( (*values)[ idx ] );
	}

	inline BF & current(avm_size_t offset)
	{
		return( (*values)[ offset ] );
	}

	inline void current(const BF & val)
	{
		(*values)[ idx ] = val;
	}

	inline void current_next(const BF & val)
	{
		(*values)[ idx ] = val;
		++idx;
	}

	inline void next()
	{
		++idx;
	}


	/**
	 * GETTER
	 */
	inline BF & operator[](avm_size_t offset)
	{
		return( (*values)[ offset ] );
	}

	inline const BF & operator[](avm_size_t offset) const
	{
		return( (*values)[ offset ] );
	}


	inline BF & at(avm_size_t offset)
	{
		return( (*values)[ offset ] );
	}

	inline const BF & at(avm_size_t offset) const
	{
		return( (*values)[ offset ] );
	}



	/**
	 * DECODE EVAL CONTEXT
	 */
	bool main_decode_eval(BFCode & inCODE);

	bool main_decode_eval_args(AvmCode * inCODE);


	bool decode_eval_args_context(AvmBytecode & bytecode, AvmCode * inCODE);

	/**
	 * DECODE EVAL PROCESSOR
	 */
	bool decode_eval_args_processor(AvmBytecode & bytecode, AvmCode * inCODE);

	bool decode_eval_processor(AvmBytecode & bytecode, AvmCode * inCODE);
	bool decode_eval_processor(AvmBytecode & bytecode, BF & arg);

	BF return_decode_eval_processor(AvmBytecode & bytecode, BF & arg);


	bool decode_eval_processor(BFCode & aCode);
	BF return_decode_eval_processor(BFCode & aCode);

	/**
	 * EVAL PROCESSOR < AVM_ARG_MEMORY_UFI_POINTER_CPU >
	 */
	bool eval_processor_dma_lvalue_ufi_pointer(AvmBytecode & bytecode, BF & arg);

	bool eval_processor_dma_wvalue_ufi_pointer(AvmBytecode & bytecode, BF & arg);

	bool eval_processor_dma_rvalue_ufi_pointer(AvmBytecode & bytecode, BF & arg);

	/**
	 * EVAL PROCESSOR < AVM_ARG_MEMORY_LVALUE_CPU >
	 */
	bool eval_processor_dma_lvalue(AvmBytecode & bytecode, BF & arg);

	/**
	 * EVAL PROCESSOR < AVM_ARG_MEMORY_WVALUE_CPU >
	 */
	bool eval_processor_dma_wvalue(AvmBytecode & bytecode, BF & arg);

	/**
	 * EVAL PROCESSOR < AVM_ARG_MEMORY_RVALUE_CPU >
	 */
	bool eval_processor_dma_rvalue(AvmBytecode & bytecode, BF & arg);
	bool eval_processor_dma_rvalue(AvmBytecode & bytecode, AvmCode * aCode);

	bool decode_eval_rvalue(BF & arg);

	BF return_decode_eval_rvalue(BF & arg);

	/**
	 * EVAL PROCESSOR < AVM_ARG_MEMORY_MACHINE_CPU >
	 */
	bool eval_processor_dma_machine(AvmBytecode & bytecode, BF & arg);
	bool eval_processor_dma_machine(AvmBytecode & bytecode, AvmCode * aCode);

	const RuntimeID & return_decode_eval_machine(const BF & anElement);

	/**
	 * EVAL PROCESSOR < AVM_ARG_ARITHMETIC_LOGIC_CPU >
	 */
	bool eval_processor_alu(AvmBytecode & bytecode, BF & arg);
	bool eval_processor_alu(AvmBytecode & bytecode, AvmCode * aCode);

	/**
	 * EVAL PROCESSOR < AVM_ARG_STATEMENT_CPU >
	 */
	bool eval_processor_statement(AvmBytecode & bytecode, AvmCode * aCode);

	/**
	 * EVAL PROCESSOR < AVM_ARG_CHARACTER_CPU >
	 */
	bool eval_processor_character(AvmBytecode & bytecode, BF & arg);
	bool eval_processor_character(AvmBytecode & bytecode, AvmCode * aCode);

	/**
	 * EVAL PROCESSOR < AVM_ARG_STRING_CPU >
	 */
	bool eval_processor_string(AvmBytecode & bytecode, BF & arg);
	bool eval_processor_string(AvmBytecode & bytecode, AvmCode * aCode);

	/**
	 * EVAL PROCESSOR < AVM_ARG_ARRAY_[L|V]_CPU >
	 */
	bool eval_processor_array_lvalue(AvmBytecode & bytecode, BF & arg);

	bool eval_processor_array_rvalue(AvmBytecode & bytecode, BF & arg);

	BF genArray(ContainerTypeSpecifier * arrayT, const BF & arg);

	bool eval_processor_array_rvalue(AvmBytecode & bytecode, AvmCode * aCode);


	/**
	 * EVAL PROCESSOR < AVM_ARG_VECTOR_CPU >
	 */
	bool eval_processor_vector(AvmBytecode & bytecode, BF & arg);
	bool eval_processor_vector(AvmBytecode & bytecode, AvmCode * aCode);


	/**
	 * EVAL PROCESSOR < AVM_ARG_QUEUE_CPU >
	 * EVAL PROCESSOR < AVM_ARG_LIST_CPU >
	 * EVAL PROCESSOR < AVM_ARG_COLLECTION_CPU >
	 */
	bool eval_processor_collection(AvmBytecode & bytecode, BF & arg);
	bool eval_processor_collection(AvmBytecode & bytecode, AvmCode * aCode);


	/**
	 * EVAL PROCESSOR < AVM_ARG_BUFFER_CPU >
	 */
	bool eval_processor_buffer(AvmBytecode & bytecode, BF & arg);
	bool eval_processor_buffer(AvmBytecode & bytecode, AvmCode * aCode);


	/**
	 * DECODE EVAL RVALUE
	 */
	BF ginac_return_decode_eval_rvalue(BF & arg);


	/**
	 * Serialization
	 */
	void argsStream(OutStream & os);


	// Attribute
	ARGS_ENV * NEXT;

	BaseEnvironment * ENV;

	APExecutionData outED;

	RuntimeID mCTX;

	Vector< BF > table;
	Vector< BF > * values;

	// Attributes
	AvmInstruction * argsInstruction;
	AvmBytecode * argsBytecode;

	avm_size_t capacity;
	avm_size_t count;
	avm_size_t idx;


	static avm_size_t CALL_COUNT;

	static avm_size_t CALL_COUNT_GINAC;

};



class InstructionEnvironment :
		public AvmObject,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( InstructionEnvironment )
{

	AVM_DECLARE_CLONABLE_CLASS( InstructionEnvironment )


public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	InstructionEnvironment(BaseEnvironment & ENV);

	InstructionEnvironment(BaseEnvironment & ENV, avm_size_t count);

	InstructionEnvironment(BaseEnvironment * ENV,
			const APExecutionData & outED, avm_size_t count)
	: AvmObject( ),
	mARG( newARGS(ENV, outED, count) ),
	itARG( mARG )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~InstructionEnvironment()
	{
		freeARGS( mARG );
	}


	/**
	 * GETTER -- SETTER
	 * value
	 */
//	inline const BF & get() const
//	{
//		return( theArg->values[ idx ] );
//	}
//
//	inline const BF & get(const avm_size_t offset) const
//	{
//		return( theArg->values[ offset ] );
//	}
//
//	inline void set(const BF & bf)
//	{
//		theArg->values[theArg->idx ] = bf;
//	}
//
//	inline void set(const avm_size_t offset, const BF & bf)
//	{
//		theArg->values[ offset ] = bf;
//	}


	/**
	 * Serialization
	 */
	inline void toStream(OutStream & os) const
	{
		//!! NOTHING
	}


	/**
	 * Attributes
	 */

	ARGS_ENV * mARG;

	ARGS_ENV * itARG;


	///////////////////////////////////////////////////////////////////////////
	// CACHE MANAGER
	///////////////////////////////////////////////////////////////////////////
	static List< ARGS_ENV * >  ARGS_ENV_CACHE;

	static void initCache();

	static void finalizeCache();


	static ARGS_ENV * newARGS(BaseEnvironment * ENV,
			const APExecutionData & anED, avm_size_t count);

	static void freeARGS(ARGS_ENV * & arg);



};



} /* namespace sep */
#endif /* INSTRUCTIONENVIRONMENT_H_ */
