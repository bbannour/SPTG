/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 16 déc. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmCodeFactory.h"

#include <fml/executable/ExecutableForm.h>
#include <fml/executable/ExecutableLib.h>

#include <fml/operator/OperatorManager.h>


namespace sep
{


/**
 * METHODS
 * flatten AvmCode
 */
BF AvmCodeFactory::flatten(BF aCode)
{
	switch( aCode.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			return( AvmCodeFactory::flattenCode( aCode.bfCode() ) );
		}

		default:
		{
			return( aCode );
		}
	}
}



BFCode AvmCodeFactory::flattenCode(BFCode anAvmCode)
{
	const Operator * anOperator = anAvmCode->getOperator();

	AvmCode::OperandCollectionT flattenArgs;
	BFCode arg;
	std::size_t flatCount = 0;

	for( const auto & itOperand : anAvmCode.getOperands() )
	{
		if( itOperand.is< AvmCode >() )
		{
			arg = AvmCodeFactory::flattenCode( itOperand.bfCode() );

			if( anOperator->isWeakAssociative() &&
				arg->isOperator( anOperator ) )
			{
				flattenArgs.append( arg->getOperands() );

				++flatCount;
			}
			else
			{
				flattenArgs.append( arg );

				if( itOperand.raw_pointer() != arg )
				{
					++flatCount;
				}
			}
		}
		else
		{
			flattenArgs.append( itOperand );
		}
	}

	if( flatCount > 0 )
	{
		if( anAvmCode->isUnique() )
		{
			anAvmCode->getOperands().clear();
			anAvmCode->append(flattenArgs);
		}
		else
		{
			anAvmCode = AvmCodeFactory::newCode(
					anAvmCode->getOperator(), flattenArgs);
		}
	}

	return( anAvmCode );
}



/**
 * METHODS
 * contains subCode with a specific operator
 */
bool AvmCodeFactory::contains(const ExecutableForm & anExecutable,
		const BFCode & aCode, AVM_OPCODE anOpcode)
{
	if( aCode.invalid() )
	{
		return( false );
	}
	else if( aCode->isOpCode(anOpcode) )
	{
		return true;
	}
	else if( OperatorManager::isActivity(aCode->getOperator())
			&& ( aCode->noOperand()
				|| (aCode->first() == ExecutableLib::MACHINE_SELF) ) )
	{
		return( contains(anExecutable,
				anExecutable.getOnActivity( aCode->getAvmOpCode() ),
				anOpcode) );
	}
	else
	{
		for( const auto & itOperand : aCode.getOperands() )
		{
			if( itOperand.is< AvmCode >() )
			{
				if( contains(anExecutable, itOperand.bfCode(), anOpcode) )
				{
					return true;
				}
			}
		}

		return( false );
	}
}


bool AvmCodeFactory::contains(const ExecutableForm & anExecutable,
		const BFCode & aCode, AVM_OPCODE anOpcode1, AVM_OPCODE anOpcode2)
{
	if( aCode.invalid() )
	{
		return( false );
	}
	else if( aCode->isOpCode(anOpcode1) || aCode->isOpCode(anOpcode2) )
	{
		return true;
	}
	else if( OperatorManager::isActivity(aCode->getOperator())
			&& ( aCode->noOperand()
				|| (aCode->first() == ExecutableLib::MACHINE_SELF) ) )
	{
		return( contains(anExecutable,
				anExecutable.getOnActivity( aCode->getAvmOpCode() ),
				anOpcode1, anOpcode2) );
	}
	else
	{
		for( const auto & itOperand : aCode.getOperands() )
		{
			if( itOperand.is< AvmCode >() )
			{
				if( contains(anExecutable,
						itOperand.bfCode(), anOpcode1, anOpcode2) )
				{
					return true;
				}
			}
		}

		return false;
	}
}



} /* namespace sep */
