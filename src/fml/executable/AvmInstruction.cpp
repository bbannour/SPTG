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

#include "AvmInstruction.h"


namespace sep
{

/**
 * compute main bytecode
 * NOPS or EVALS
 */
void AvmInstruction::computeMainBytecode(
		bool updateMainByteCodeIfNOPS, avm_arg_operation_t opMask)
{
	bool isUnsetNops = true;

	for( long pc = long(mSize) - 1 ; pc >= 0 ; --pc )
	{
		if( isUnsetNops && mArgBytecode[pc].isEval() )
		{
			isUnsetNops = false;

			if( pc < (long(mSize) - 2) )
			{
				mArgBytecode[pc+1].setNopsOperation();
			}
		}

		if( mArgBytecode[pc].isSeval() )
		{
			mMainBytecode.xsetSeval(opMask);
			break;
		}
		else if( mArgBytecode[pc].isMeval() )
		{
			mMainBytecode.xsetMeval(opMask);
			break;
		}
	}

	if( isUnsetNops )
	{
		mArgBytecode[0].setNopsOperation(AVM_ARG_VALUE);

		if( updateMainByteCodeIfNOPS )
		{
			mMainBytecode.setNopsOperation(opMask);
		}
	}
	else
	{
//		mMainBytecode.unsetNops();
	}
}


void AvmInstruction::computeBytecode(bool updateMainByteCodeIfNOPS,
			const Vector< AvmBytecode > & vectorOfArgOpcode)
{
	AVM_OS_ASSERT_WARNING_ALERT( vectorOfArgOpcode.nonempty() )
			<< "AvmBytecode::computeArgCode :> "
				"Unexpected an empty vector of ArgOpcode !!!"
			<< SEND_ALERT;

	mSize = vectorOfArgOpcode.size();

	if( mArgBytecode != nullptr )
	{
		delete mArgBytecode;
	}

	if( mSize > 0 )
	{
		mArgBytecode = new AvmBytecode[mSize];

		bool isUnsetNops = true;

		for( long pc = long(mSize) - 1 ; pc >= 0 ; --pc )
		{
			mArgBytecode[pc] = vectorOfArgOpcode[pc];

			if( (not isUnsetNops) && mArgBytecode[pc].isNopAllOperation() )
			{
				mArgBytecode[pc].unsetNopAllOperation();
			}

			if( isUnsetNops && mArgBytecode[pc].isEval() )
			{
				isUnsetNops = false;

				if( pc < (long(mSize) - 2) )
				{
					mArgBytecode[pc+1].setNopsOperation();
				}
			}

			if( mArgBytecode[pc].isSeval() )
			{
				if( not mMainBytecode.isMeval() )
				{
					mMainBytecode.xsetSeval();
				}
			}
			else if( mArgBytecode[pc].isMeval() &&
					(not mMainBytecode.isMeval()) )
			{
				mMainBytecode.xsetMeval();
			}
		}

		if( isUnsetNops )
		{
			mArgBytecode[0].setNopsOperation(AVM_ARG_VALUE);

			if( updateMainByteCodeIfNOPS )
			{
				mMainBytecode.setNopsOperation();
			}
		}
		else
		{
//			mMainBytecode.unsetNops();
		}
	}
	else
	{
		mMainBytecode.setNopsOperation();
	}
}


/**
 * nops bytecode
 */
AvmInstruction * AvmInstruction::nopsUnaryCode(avm_arg_operand_t operand)
{
	AvmInstruction * nopsInstruction = new AvmInstruction(1);

	nopsInstruction->setMainBytecode(
			/*processor*/ AVM_ARG_NOP_CPU,
			/*operation*/ AVM_ARG_NOPS_VALUE,
			/*operand  */ operand);

	nopsInstruction->set(0,
			/*processor*/ AVM_ARG_NOP_CPU,
			/*operation*/ AVM_ARG_NOPS_VALUE,
			/*operand  */ operand);

	return( nopsInstruction );

}


/**
 ***************************************************************************
 * SERIALIZATION
 ***************************************************************************
 */
void AvmInstruction::toStream(OutStream & os) const
{
	os << TAB << "#{" << EOL;
	for( std::size_t idx = 0 ; idx < mSize ; ++idx )
	{
		os << TAB2 << idx << ":" << mArgBytecode[idx].strCode() << EOL;
	}
	os << TAB << "}" << EOL_FLUSH;
}


} /* namespace sep */
