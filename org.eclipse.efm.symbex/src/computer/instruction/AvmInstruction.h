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

#include <computer/instruction/AvmBytecode.h>


namespace sep
{


class ARGS_ENV;
class AvmCode;
class BF;

class AvmInstruction
{

public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmInstruction()
	: theSize( 0 ),
	theMainBytecode( ),
	theArgBytecode( NULL ),

	routine_decode_eval( NULL ),
	routine_eval( NULL ),
	routine_decode_run( NULL ),
	routine_run( NULL )
	{
		//!!! NOTHING
	}

	AvmInstruction(avm_size_t aSize)
	: theSize( aSize ),
	theMainBytecode( ),
	theArgBytecode( (aSize > 0) ? new AvmBytecode[aSize] : NULL ),

	routine_decode_eval( NULL ),
	routine_eval( NULL ),
	routine_decode_run( NULL ),
	routine_run( NULL )
	{
		//!!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	explicit AvmInstruction(const AvmInstruction & anInstruction)
	: theSize( anInstruction.theSize ),
	theMainBytecode( anInstruction.theMainBytecode ),
	theArgBytecode( (theSize > 0) ? new AvmBytecode[theSize] : NULL ),

	routine_decode_eval( anInstruction.routine_decode_eval ),
	routine_eval( anInstruction.routine_eval ),
	routine_decode_run( anInstruction.routine_decode_run ),
	routine_run( anInstruction.routine_run )
	{
		copy( anInstruction.theArgBytecode );
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~AvmInstruction()
	{
		delete ( theArgBytecode );
	}


	/**
	 * copy
	 */
	inline void copy(AvmBytecode * argBytecode)
	{
		for( avm_size_t idx = 0 ; idx < theSize ; ++idx )
		{
			theArgBytecode[idx] = argBytecode[idx];
		}
	}

	inline void copy(const avm_size_t srcOffset, const avm_size_t tgtOffset)
	{
		theArgBytecode[tgtOffset] = theArgBytecode[srcOffset];
	}


	/**
	 * GETTER
	 * theSize
	 */
	inline avm_size_t size() const
	{
		return( theSize );
	}

	inline bool empty() const
	{
		return( theSize == 0 );
	}

	inline bool nonempty() const
	{
		return( theSize > 0 );
	}

	inline bool singleton() const
	{
		return( theSize == 1 );
	}

	inline bool populated() const
	{
		return( theSize > 1 );
	}


	/**
	 * GETTER - SETTER
	 * for theMainBytecode
	 */
	inline AvmBytecode & getMainBytecode()
	{
		return( theMainBytecode );
	}

	inline void setMainBytecode(AvmBytecode & aByteCode)
	{
		theMainBytecode = aByteCode;
	}


	inline void setMainBytecode(
			avm_arg_context_t context, avm_arg_processor_t processor,
			avm_arg_operation_t operation, avm_arg_operand_t operand,
			BaseTypeSpecifier * dtype = NULL)
	{
		theMainBytecode.context   = context;
		theMainBytecode.processor = processor;
		theMainBytecode.operation = operation;
		theMainBytecode.operand   = operand;
		theMainBytecode.dtype     = dtype;
	}

	inline void setMainBytecode(
			avm_arg_context_t context, avm_arg_operation_t operation,
			avm_arg_operand_t operand, BaseTypeSpecifier * dtype = NULL)
	{
		theMainBytecode.context   = context;
		theMainBytecode.operation = operation;
		theMainBytecode.operand   = operand;
		theMainBytecode.dtype     = dtype;
	}

	inline void setMainBytecode(
			avm_arg_processor_t processor, avm_arg_operation_t operation,
			avm_arg_operand_t operand, BaseTypeSpecifier * dtype = NULL)
	{
		theMainBytecode.processor = processor;
		theMainBytecode.operation = operation;
		theMainBytecode.operand   = operand;
		theMainBytecode.dtype     = dtype;
	}

	inline void setMainBytecode(avm_arg_operation_t operation,
			avm_arg_operand_t operand, BaseTypeSpecifier * dtype = NULL)
	{
		theMainBytecode.operation = operation;
		theMainBytecode.operand   = operand;
		theMainBytecode.dtype     = dtype;
	}


	inline avm_arg_context_t getMainContext() const
	{
		return( theMainBytecode.context  );
	}

	inline void setMainContext(avm_arg_context_t context)
	{
		theMainBytecode.context = context;
	}


	inline avm_arg_processor_t getMainProcessor() const
	{
		return( theMainBytecode.processor  );
	}

	inline void setMainProcessor(avm_arg_processor_t processor)
	{
		theMainBytecode.processor = processor;
	}


	inline avm_arg_operation_t getMainOperation() const
	{
		return( theMainBytecode.operation  );
	}

	inline void setMainOperation(avm_arg_operation_t operation)
	{
		theMainBytecode.operation = operation;
	}


	inline avm_arg_operand_t getMainOperand() const
	{
		return( theMainBytecode.operand  );
	}

	inline void setMainOperand(avm_arg_operand_t operand)
	{
		theMainBytecode.operand = operand;
	}


	/**
	 * theMainBytecode
	 * NOP
	 */
	inline bool isNop() const
	{
		return( IS_ARG_OPERATION_NOP(theMainBytecode.operation) );
	}

	inline void setNop(avm_arg_operation_t opMask = AVM_ARG_UNDEFINED_OPERATION)
	{
		theMainBytecode.operation = avm_arg_operation_t(
				theMainBytecode.operation | opMask | AVM_ARG_NOP );

		theMainBytecode.operation = avm_arg_operation_t(
				theMainBytecode.operation & (~AVM_ARG_OPERATION_EVAL_MASK) );
	}


	/**
	 * theMainBytecode
	 * NOPS
	 */
	inline bool isNopCPU() const
	{
		return( theMainBytecode.processor == AVM_ARG_NOP_CPU );
	}

	inline bool isNops() const
	{
		return( IS_ARG_OPERATION_NOPS(theMainBytecode.operation) );
	}

	inline void setNops(avm_arg_operation_t opMask = AVM_ARG_UNDEFINED_OPERATION)
	{
		theMainBytecode.operation = avm_arg_operation_t(
				theMainBytecode.operation | opMask | AVM_ARG_NOPS );

		theMainBytecode.operation = avm_arg_operation_t(
				theMainBytecode.operation & (~AVM_ARG_OPERATION_EVAL_MASK) );
	}

	inline void unsetNops(avm_arg_operation_t opMask = AVM_ARG_SEVAL)
	{
		theMainBytecode.operation = avm_arg_operation_t(
				(theMainBytecode.operation | opMask) &
				(~ AVM_ARG_OPERATION_NOP_MASK) );
	}


	/**
	 * theMainBytecode
	 * EVAL
	 * EVAL
	 */
	inline bool isEval() const
	{
		return( IS_ARG_OPERATION_EVAL(theMainBytecode.operation) );
	}

	inline void unsetEval()
	{
		theMainBytecode.operation = avm_arg_operation_t(
				theMainBytecode.operation & (~ AVM_ARG_OPERATION_EVAL_MASK) );
	}


	/**
	 * theMainBytecode
	 * SEVAL
	 */
	inline bool isSeval() const
	{
		return( IS_ARG_OPERATION_SEVAL(theMainBytecode.operation) );
	}

	inline void setSeval(avm_arg_operation_t opMask = AVM_ARG_UNDEFINED_OPERATION)
	{
		theMainBytecode.operation = avm_arg_operation_t(
				theMainBytecode.operation | opMask | AVM_ARG_SEVAL);
	}

	// eXclusive PREFIX bit setting
	inline void xsetSeval(avm_arg_operation_t opMask = AVM_ARG_UNDEFINED_OPERATION)
	{
		theMainBytecode.operation = avm_arg_operation_t(
				(theMainBytecode.operation | opMask) &
				AVM_ARG_OPERATION_X_SEVAL_MASK );
	}

	inline void unsetSeval()
	{
		theMainBytecode.operation = avm_arg_operation_t(
				theMainBytecode.operation & (~ AVM_ARG_SEVAL) );
	}


	/**
	 * theMainBytecode
	 * MEVAL
	 */
	inline bool isMeval() const
	{
		return( IS_ARG_OPERATION_MEVAL(theMainBytecode.operation) );
	}

	inline void setMeval(avm_arg_operation_t opMask = AVM_ARG_UNDEFINED_OPERATION)
	{
		theMainBytecode.operation = avm_arg_operation_t(
				theMainBytecode.operation | opMask | AVM_ARG_MEVAL);
	}

	// eXclusive PREFIX bit setting
	inline void xsetMeval(avm_arg_operation_t opMask = AVM_ARG_UNDEFINED_OPERATION)
	{
		theMainBytecode.operation = avm_arg_operation_t(
				(theMainBytecode.operation | opMask) &
				AVM_ARG_OPERATION_X_MEVAL_MASK );
	}

	inline void unsetMeval()
	{
		theMainBytecode.operation = avm_arg_operation_t(
				theMainBytecode.operation & (~ AVM_ARG_MEVAL) );
	}


	/**
	 * GETTER - SETTER
	 * for theArgBytecode
	 */
	inline AvmBytecode * getBytecode() const
	{
		return( theArgBytecode );
	}

	inline bool hasBytecode() const
	{
		return( theArgBytecode != NULL );
	}

	inline void setBytecode(AvmBytecode * anBytecode)
	{
		theArgBytecode = anBytecode;
	}

	/**
	 * GETTER
	 * for theArgBytecode w.r.t. an idx
	 */
	inline AvmBytecode & operator[](avm_size_t idx)
	{
		return( theArgBytecode[idx] );
	}

	inline const AvmBytecode & operator[](avm_size_t idx) const
	{
		return( theArgBytecode[idx] );
	}


	inline AvmBytecode & at(const avm_size_t idx)
	{
		return( theArgBytecode[idx] );
	}

	inline const AvmBytecode & at(const avm_size_t idx) const
	{
		return( theArgBytecode[idx] );
	}

	inline AvmBytecode & get(const avm_size_t idx)
	{
		return( theArgBytecode[idx] );
	}

	inline const AvmBytecode & get(const avm_size_t idx) const
	{
		return( theArgBytecode[idx] );
	}


	/**
	 * SETTER
	 * for theArgBytecode w.r.t. an idx
	 */
	inline void set(const avm_size_t idx, AvmBytecode & aByteCode)
	{
		theArgBytecode[idx] = aByteCode;
	}

	inline void set(const avm_size_t idx, avm_arg_context_t context,
			avm_arg_processor_t processor, avm_arg_operation_t operation,
			avm_arg_operand_t operand, BaseTypeSpecifier * dtype = NULL)
	{
		theArgBytecode[idx].context   = context;
		theArgBytecode[idx].processor = processor;
		theArgBytecode[idx].operation = operation;
		theArgBytecode[idx].operand   = operand;
		theArgBytecode[idx].dtype     = dtype;
	}

	inline void set(const avm_size_t idx,
			avm_arg_processor_t processor, avm_arg_operation_t operation,
			avm_arg_operand_t operand, BaseTypeSpecifier * dtype = NULL)
	{
		theArgBytecode[idx].processor = processor;
		theArgBytecode[idx].operation = operation;
		theArgBytecode[idx].operand   = operand;
		theArgBytecode[idx].dtype     = dtype;
	}

	inline void set(const avm_size_t idx, avm_arg_operation_t operation,
			avm_arg_operand_t operand, BaseTypeSpecifier * dtype = NULL)
	{
		theArgBytecode[idx].operation = operation;
		theArgBytecode[idx].operand   = operand;
		theArgBytecode[idx].dtype     = dtype;
	}


	inline avm_arg_context_t context(const avm_size_t idx)
	{
		return( theArgBytecode[idx].context );
	}

	inline void context(const avm_size_t idx, avm_arg_context_t context)
	{
		theArgBytecode[idx].context = context;
	}


	inline avm_arg_processor_t processor(const avm_size_t idx)
	{
		return( theArgBytecode[idx].processor );
	}

	inline void processor(const avm_size_t idx, avm_arg_processor_t processor)
	{
		theArgBytecode[idx].processor = processor;
	}


	inline avm_arg_operation_t operation(const avm_size_t idx)
	{
		return( theArgBytecode[idx].operation );
	}

	inline void operation(const avm_size_t idx, avm_arg_operation_t operation)
	{
		theArgBytecode[idx].operation = operation;
	}


	inline avm_arg_operand_t operand(const avm_size_t idx)
	{
		return( theArgBytecode[idx].operand );
	}

	inline void operand(const avm_size_t idx, avm_arg_operand_t operand)
	{
		theArgBytecode[idx].operand = operand;
	}



	inline avm_size_t offset(const avm_size_t idx)
	{
		return( theArgBytecode[idx].offset );
	}

	inline void offset(const avm_size_t idx, avm_size_t offset)
	{
		theArgBytecode[idx].offset = offset;
	}


	inline BaseTypeSpecifier * dtype(const avm_size_t idx)
	{
		return( theArgBytecode[idx].dtype );
	}

	inline void dtype(const avm_size_t idx, BaseTypeSpecifier * dtype)
	{
		theArgBytecode[idx].dtype = dtype;
	}


	/**
	 * compute main bytecode
	 * NOPS or EVALS
	 */
	void computeMainBytecode(
			bool updateMainByteCodeIfNOPS, avm_arg_operation_t opMask);

	inline void computeMainBytecode(avm_arg_context_t aContext,
			avm_arg_processor_t aProcessor, avm_arg_operation_t anOperation,
			avm_arg_operand_t anOperand, BaseTypeSpecifier * aType = NULL)
	{
		theMainBytecode.context   = aContext;
		theMainBytecode.processor = aProcessor;
		theMainBytecode.operation = anOperation;
		theMainBytecode.operand   = anOperand;
		theMainBytecode.dtype     = aType;

		computeMainBytecode(true, AVM_ARG_UNDEFINED_OPERATION);
	}

	inline void computeMainBytecode(avm_size_t refBytecodeOffset)
	{
		theMainBytecode = theArgBytecode[ refBytecodeOffset ];

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
	avm_size_t theSize;

	AvmBytecode theMainBytecode;

	AvmBytecode * theArgBytecode;


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
