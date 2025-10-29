/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 23 janv. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVMINSTRUCTION_H_
#define AVMINSTRUCTION_H_

#include <collection/Vector.h>

#include <fml/executable/AvmBytecode.h>


namespace sep
{


class ARGS_ENV;
class AvmCode;
class BF;

class TypeSpecifier;


class AvmInstruction final
{

public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmInstruction()
	: mSize( 0 ),
	mMainBytecode( ),
	mArgBytecode( nullptr ),

	routine_decode_eval( nullptr ),
	routine_eval( nullptr ),
	routine_decode_run( nullptr ),
	routine_run( nullptr )
	{
		//!!! NOTHING
	}

	AvmInstruction(std::size_t aSize)
	: mSize( aSize ),
	mMainBytecode( ),
	mArgBytecode( (aSize > 0) ? new AvmBytecode[aSize] : nullptr ),

	routine_decode_eval( nullptr ),
	routine_eval( nullptr ),
	routine_decode_run( nullptr ),
	routine_run( nullptr )
	{
		//!!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	explicit AvmInstruction(const AvmInstruction & anInstruction)
	: mSize( anInstruction.mSize ),
	mMainBytecode( anInstruction.mMainBytecode ),
	mArgBytecode( (mSize > 0) ? new AvmBytecode[mSize] : nullptr ),

	routine_decode_eval( anInstruction.routine_decode_eval ),
	routine_eval( anInstruction.routine_eval ),
	routine_decode_run( anInstruction.routine_decode_run ),
	routine_run( anInstruction.routine_run )
	{
		copy( anInstruction.mArgBytecode );
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~AvmInstruction()
	{
		delete ( mArgBytecode );
	}


	/**
	 * copy
	 */
	inline void copy(AvmBytecode * argBytecode)
	{
		for( std::size_t idx = 0 ; idx < mSize ; ++idx )
		{
			mArgBytecode[idx] = argBytecode[idx];
		}
	}

	inline void copy(const std::size_t srcOffset, const std::size_t tgtOffset)
	{
		mArgBytecode[tgtOffset] = mArgBytecode[srcOffset];
	}


	/**
	 * GETTER
	 * mSize
	 */
	inline std::size_t size() const
	{
		return( mSize );
	}

	inline bool empty() const
	{
		return( mSize == 0 );
	}

	inline bool nonempty() const
	{
		return( mSize > 0 );
	}

	inline bool singleton() const
	{
		return( mSize == 1 );
	}

	inline bool populated() const
	{
		return( mSize > 1 );
	}


	/**
	 * GETTER - SETTER
	 * for mMainBytecode
	 */
	inline AvmBytecode & getMainBytecode()
	{
		return( mMainBytecode );
	}

	inline void setMainBytecode(AvmBytecode & aByteCode)
	{
		mMainBytecode = aByteCode;
	}


	inline void setMainBytecode(
			avm_arg_context_t context, avm_arg_processor_t processor,
			avm_arg_operation_t operation, avm_arg_operand_t operand,
			const BaseTypeSpecifier & dtype)
	{
		mMainBytecode.context   = context;
		mMainBytecode.processor = processor;
		mMainBytecode.operation = operation;
		mMainBytecode.operand   = operand;
		mMainBytecode.dtype     = (& dtype);
	}

	inline void setMainBytecode(
			avm_arg_context_t context, avm_arg_processor_t processor,
			avm_arg_operation_t operation, avm_arg_operand_t operand,
			const BaseTypeSpecifier * dtype)
	{
		mMainBytecode.context   = context;
		mMainBytecode.processor = processor;
		mMainBytecode.operation = operation;
		mMainBytecode.operand   = operand;
		mMainBytecode.dtype     = dtype;
	}


	inline void setMainBytecode(avm_arg_processor_t processor,
			avm_arg_operation_t operation, avm_arg_operand_t operand)
	{
		mMainBytecode.processor = processor;
		mMainBytecode.operation = operation;
		mMainBytecode.operand   = operand;
		mMainBytecode.dtype     = nullptr;
	}


	inline void setMainBytecode(
			avm_arg_operation_t operation, avm_arg_operand_t operand)
	{
		mMainBytecode.operation = operation;
		mMainBytecode.operand   = operand;
		mMainBytecode.dtype     = nullptr;
	}


	inline avm_arg_context_t getMainContext() const
	{
		return( mMainBytecode.context  );
	}

	inline void setMainContext(avm_arg_context_t context)
	{
		mMainBytecode.context = context;
	}


	inline avm_arg_processor_t getMainProcessor() const
	{
		return( mMainBytecode.processor  );
	}

	inline void setMainProcessor(avm_arg_processor_t processor)
	{
		mMainBytecode.processor = processor;
	}


	inline avm_arg_operation_t getMainOperation() const
	{
		return( mMainBytecode.operation  );
	}

	inline void setMainOperation(avm_arg_operation_t operation)
	{
		mMainBytecode.operation = operation;
	}


	inline avm_arg_operand_t getMainOperand() const
	{
		return( mMainBytecode.operand  );
	}

	inline void setMainOperand(avm_arg_operand_t operand)
	{
		mMainBytecode.operand = operand;
	}


	/**
	 * mMainBytecode
	 * NOP
	 */
	inline bool isNop() const
	{
		return( IS_ARG_OPERATION_NOP(mMainBytecode.operation) );
	}

	inline void setNop(avm_arg_operation_t opMask = AVM_ARG_UNDEFINED_OPERATION)
	{
		mMainBytecode.operation = avm_arg_operation_t(
				mMainBytecode.operation | opMask | AVM_ARG_NOP );

		mMainBytecode.operation = avm_arg_operation_t(
				mMainBytecode.operation & (~AVM_ARG_OPERATION_EVAL_MASK) );
	}


	/**
	 * mMainBytecode
	 * NOPS
	 */
	inline bool isNopCPU() const
	{
		return( mMainBytecode.processor == AVM_ARG_NOP_CPU );
	}

	inline bool isNops() const
	{
		return( IS_ARG_OPERATION_NOPS(mMainBytecode.operation) );
	}

	inline void setNops(avm_arg_operation_t opMask = AVM_ARG_UNDEFINED_OPERATION)
	{
		mMainBytecode.operation = avm_arg_operation_t(
				mMainBytecode.operation | opMask | AVM_ARG_NOPS );

		mMainBytecode.operation = avm_arg_operation_t(
				mMainBytecode.operation & (~AVM_ARG_OPERATION_EVAL_MASK) );
	}

	inline void unsetNops(avm_arg_operation_t opMask = AVM_ARG_SEVAL)
	{
		mMainBytecode.operation = avm_arg_operation_t(
				(mMainBytecode.operation | opMask) &
				(~ AVM_ARG_OPERATION_NOP_MASK) );
	}


	/**
	 * mMainBytecode
	 * EVAL
	 * EVAL
	 */
	inline bool isEval() const
	{
		return( IS_ARG_OPERATION_EVAL(mMainBytecode.operation) );
	}

	inline void unsetEval()
	{
		mMainBytecode.operation = avm_arg_operation_t(
				mMainBytecode.operation & (~ AVM_ARG_OPERATION_EVAL_MASK) );
	}


	/**
	 * mMainBytecode
	 * SEVAL
	 */
	inline bool isSeval() const
	{
		return( IS_ARG_OPERATION_SEVAL(mMainBytecode.operation) );
	}

	inline void setSeval(avm_arg_operation_t opMask = AVM_ARG_UNDEFINED_OPERATION)
	{
		mMainBytecode.operation = avm_arg_operation_t(
				mMainBytecode.operation | opMask | AVM_ARG_SEVAL);
	}

	// eXclusive PREFIX bit setting
	inline void xsetSeval(avm_arg_operation_t opMask = AVM_ARG_UNDEFINED_OPERATION)
	{
		mMainBytecode.operation = avm_arg_operation_t(
				(mMainBytecode.operation | opMask) &
				AVM_ARG_OPERATION_X_SEVAL_MASK );
	}

	inline void unsetSeval()
	{
		mMainBytecode.operation = avm_arg_operation_t(
				mMainBytecode.operation & (~ AVM_ARG_SEVAL) );
	}


	/**
	 * mMainBytecode
	 * MEVAL
	 */
	inline bool isMeval() const
	{
		return( IS_ARG_OPERATION_MEVAL(mMainBytecode.operation) );
	}

	inline void setMeval(avm_arg_operation_t opMask = AVM_ARG_UNDEFINED_OPERATION)
	{
		mMainBytecode.operation = avm_arg_operation_t(
				mMainBytecode.operation | opMask | AVM_ARG_MEVAL);
	}

	// eXclusive PREFIX bit setting
	inline void xsetMeval(avm_arg_operation_t opMask = AVM_ARG_UNDEFINED_OPERATION)
	{
		mMainBytecode.operation = avm_arg_operation_t(
				(mMainBytecode.operation | opMask) &
				AVM_ARG_OPERATION_X_MEVAL_MASK );
	}

	inline void unsetMeval()
	{
		mMainBytecode.operation = avm_arg_operation_t(
				mMainBytecode.operation & (~ AVM_ARG_MEVAL) );
	}


	/**
	 * GETTER - SETTER
	 * for mArgBytecode
	 */
	inline AvmBytecode * getBytecode() const
	{
		return( mArgBytecode );
	}

	inline bool hasBytecode() const
	{
		return( mArgBytecode != nullptr );
	}

	inline void setBytecode(AvmBytecode * anBytecode)
	{
		mArgBytecode = anBytecode;
	}

	/**
	 * GETTER
	 * for mArgBytecode w.r.t. an idx
	 */
	inline AvmBytecode & operator[](std::size_t idx)
	{
		return( mArgBytecode[idx] );
	}

	inline const AvmBytecode & operator[](std::size_t idx) const
	{
		return( mArgBytecode[idx] );
	}


	inline AvmBytecode & at(const std::size_t idx)
	{
		return( mArgBytecode[idx] );
	}

	inline const AvmBytecode & at(const std::size_t idx) const
	{
		return( mArgBytecode[idx] );
	}

	inline AvmBytecode & get(const std::size_t idx)
	{
		return( mArgBytecode[idx] );
	}

	inline const AvmBytecode & get(const std::size_t idx) const
	{
		return( mArgBytecode[idx] );
	}


	/**
	 * SETTER
	 * for mArgBytecode w.r.t. an idx
	 */
	inline void set(const std::size_t idx, AvmBytecode & aByteCode)
	{
		mArgBytecode[idx] = aByteCode;
	}

	inline void set(const std::size_t idx, avm_arg_context_t context,
			avm_arg_processor_t processor, avm_arg_operation_t operation,
			avm_arg_operand_t operand)
	{
		mArgBytecode[idx].context   = context;
		mArgBytecode[idx].processor = processor;
		mArgBytecode[idx].operation = operation;
		mArgBytecode[idx].operand   = operand;
		mArgBytecode[idx].dtype     = nullptr;
	}

	inline void set(const std::size_t idx, avm_arg_context_t context,
			avm_arg_processor_t processor, avm_arg_operation_t operation,
			avm_arg_operand_t operand, const BaseTypeSpecifier & dtype)
	{
		mArgBytecode[idx].context   = context;
		mArgBytecode[idx].processor = processor;
		mArgBytecode[idx].operation = operation;
		mArgBytecode[idx].operand   = operand;
		mArgBytecode[idx].dtype     = (& dtype);
	}


	inline void set(const std::size_t idx, avm_arg_processor_t processor,
			avm_arg_operation_t operation, avm_arg_operand_t operand)
	{
		mArgBytecode[idx].processor = processor;
		mArgBytecode[idx].operation = operation;
		mArgBytecode[idx].operand   = operand;
		mArgBytecode[idx].dtype     = nullptr;
	}

	inline void set(const std::size_t idx, avm_arg_processor_t processor,
			avm_arg_operation_t operation, avm_arg_operand_t operand,
			const BaseTypeSpecifier & dtype)
	{
		mArgBytecode[idx].processor = processor;
		mArgBytecode[idx].operation = operation;
		mArgBytecode[idx].operand   = operand;
		mArgBytecode[idx].dtype     = (& dtype);
	}


	inline void set(const std::size_t idx,
			avm_arg_operation_t operation, avm_arg_operand_t operand)
	{
		mArgBytecode[idx].operation = operation;
		mArgBytecode[idx].operand   = operand;
		mArgBytecode[idx].dtype     = nullptr;
	}

	inline void set(const std::size_t idx, avm_arg_operation_t operation,
			avm_arg_operand_t operand, const BaseTypeSpecifier & dtype)
	{
		mArgBytecode[idx].operation = operation;
		mArgBytecode[idx].operand   = operand;
		mArgBytecode[idx].dtype     = (& dtype);
	}


	inline avm_arg_context_t context(const std::size_t idx)
	{
		return( mArgBytecode[idx].context );
	}

	inline void context(const std::size_t idx, avm_arg_context_t context)
	{
		mArgBytecode[idx].context = context;
	}


	inline avm_arg_processor_t processor(const std::size_t idx)
	{
		return( mArgBytecode[idx].processor );
	}

	inline void processor(const std::size_t idx, avm_arg_processor_t processor)
	{
		mArgBytecode[idx].processor = processor;
	}


	inline avm_arg_operation_t operation(const std::size_t idx)
	{
		return( mArgBytecode[idx].operation );
	}

	inline void operation(const std::size_t idx, avm_arg_operation_t operation)
	{
		mArgBytecode[idx].operation = operation;
	}


	inline avm_arg_operand_t operand(const std::size_t idx)
	{
		return( mArgBytecode[idx].operand );
	}

	inline void operand(const std::size_t idx, avm_arg_operand_t operand)
	{
		mArgBytecode[idx].operand = operand;
	}



	inline std::size_t offset(const std::size_t idx)
	{
		return( mArgBytecode[idx].offset );
	}

	inline void offset(const std::size_t idx, std::size_t offset)
	{
		mArgBytecode[idx].offset = offset;
	}


	inline const BaseTypeSpecifier * dtype(const std::size_t idx)
	{
		return( mArgBytecode[idx].dtype );
	}

	inline void dtype(const std::size_t idx, const BaseTypeSpecifier & dtype)
	{
		mArgBytecode[idx].dtype = (& dtype);
	}


	/**
	 * compute main bytecode
	 * NOPS or EVALS
	 */
	void computeMainBytecode(
			bool updateMainByteCodeIfNOPS, avm_arg_operation_t opMask);

	inline void computeMainBytecode(
			avm_arg_context_t aContext, avm_arg_processor_t aProcessor,
			avm_arg_operation_t anOperation, avm_arg_operand_t anOperand,
			const BaseTypeSpecifier * aType = nullptr)
	{
		mMainBytecode.context   = aContext;
		mMainBytecode.processor = aProcessor;
		mMainBytecode.operation = anOperation;
		mMainBytecode.operand   = anOperand;
		mMainBytecode.dtype     = aType;

		computeMainBytecode(true, AVM_ARG_UNDEFINED_OPERATION);
	}

	inline void computeMainBytecode(std::size_t refBytecodeOffset)
	{
		mMainBytecode = mArgBytecode[ refBytecodeOffset ];

		computeMainBytecode(true, AVM_ARG_UNDEFINED_OPERATION);
	}


	void computeBytecode(bool updateMainByteCodeIfNOPS,
			const Vector< AvmBytecode > & vectorOfArgOpcode);


	/**
	 * nops bytecode
	 */
	static AvmInstruction * nopsUnaryCode(avm_arg_operand_t operand);


	/**
	 ***************************************************************************
	 * SERIALIZATION
	 ***************************************************************************
	 */
	void toStream(OutStream & os) const;


protected:
	/**
	 * ATTRIBUTES
	 */
	std::size_t mSize;

	AvmBytecode mMainBytecode;

	AvmBytecode * mArgBytecode;


public:
	////////////////////////////////////////////////////////////////////////////
	// optimize API for << [decode] eval >> routine
	////////////////////////////////////////////////////////////////////////////

	bool (* routine_decode_eval)(AvmInstruction *, ARGS_ENV &, const BF &);

	inline bool decode_eval(ARGS_ENV & argENV, const BF & arg)
	{
		return( routine_decode_eval(this, argENV, arg) );
	}


	bool (* routine_eval)(AvmInstruction *, ARGS_ENV &, AvmCode *);

	inline bool eval(ARGS_ENV & argENV, AvmCode * aCode)
	{
		return( routine_eval(this, argENV, aCode) );
	}


	////////////////////////////////////////////////////////////////////////////
	// optimize API for << [decode] rrun >> routine
	////////////////////////////////////////////////////////////////////////////

	bool (* routine_decode_run)(AvmInstruction *, ARGS_ENV &, const BF &);

	inline bool decode_run(ARGS_ENV & argENV, const BF & arg)
	{
		return( routine_decode_run(this, argENV, arg) );
	}


	bool (* routine_run)(AvmInstruction *, ARGS_ENV & argENV, AvmCode *);

	inline bool run(ARGS_ENV & argENV, AvmCode * aCode)
	{
		return( routine_run(this, argENV, aCode) );
	}


};


} /* namespace sep */

#endif /* AVMINSTRUCTION_H_ */
