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

#include <fml/expression/AvmCode.h>


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
	for( int pc = int(theSize) - 1 ; pc >= 0 ; --pc )
	{
		if( isUnsetNops && theArgBytecode[pc].isEval() )
		{
			isUnsetNops = false;

			if( pc < (int(theSize) - 2) )
			{
				theArgBytecode[pc+1].setNopsOperation();
			}
		}

		if( theArgBytecode[pc].isSeval() )
		{
			theMainBytecode.xsetSeval(opMask);
		}
		else if( theArgBytecode[pc].isMeval() )
		{
			theMainBytecode.xsetMeval(opMask);
			break;
		}
	}

	if( isUnsetNops )
	{
		theArgBytecode[0].setNopsOperation(AVM_ARG_VALUE);

		if( updateMainByteCodeIfNOPS )
		{
			theMainBytecode.setNopsOperation(opMask);
		}
	}
	else
	{
//		theMainBytecode.unsetNops();
	}
}


void AvmInstruction::computeBytecode(bool updateMainByteCodeIfNOPS,
			const Vector< AvmBytecode > & vectorOfArgOpcode)
{
	AVM_OS_ASSERT_WARNING_ALERT( vectorOfArgOpcode.nonempty() )
			<< "AvmBytecode::computeArgCode :> "
				"Unexpected an empty vector of ArgOpcode !!!"
			<< SEND_ALERT;

	theSize = vectorOfArgOpcode.size();

	if( theArgBytecode != NULL )
	{
		delete theArgBytecode;
	}

	if( theSize > 0 )
	{
		theArgBytecode = new AvmBytecode[theSize];

//		for( avm_size_t pc = 0 ; pc < count ; ++pc )
//		{
//			theArgBytecode[pc] = vectorOfArgOpcode[pc];
//		}

		bool isUnsetNops = true;
		for( int pc = int(theSize) - 1 ; pc >= 0 ; --pc )
		{
			theArgBytecode[pc] = vectorOfArgOpcode[pc];

			if( isUnsetNops && theArgBytecode[pc].isEval() )
			{
				isUnsetNops = false;

				if( pc < (int(theSize) - 2) )
				{
					theArgBytecode[pc+1].setNopsOperation();
				}
			}

			if( theArgBytecode[pc].isSeval() )
			{
				if( not theMainBytecode.isMeval() )
				{
					theMainBytecode.xsetSeval();
				}
			}
			else if( theArgBytecode[pc].isMeval() &&
					(not theMainBytecode.isMeval()) )
			{
				theMainBytecode.xsetMeval();
			}
		}

		if( isUnsetNops )
		{
			theArgBytecode[0].setNopsOperation(AVM_ARG_VALUE);

			if( updateMainByteCodeIfNOPS )
			{
				theMainBytecode.setNopsOperation();
			}
		}
		else
		{
//			theMainBytecode.unsetNops();
		}
	}
	else
	{
		theMainBytecode.setNopsOperation();
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
	for( avm_size_t idx = 0 ; idx < theSize ; ++idx )
	{
		os << TAB2 << idx << ":" << theArgBytecode[idx].strCode() << EOL;
	}
	os << TAB << "}" << EOL_FLUSH;
}


} /* namespace sep */
