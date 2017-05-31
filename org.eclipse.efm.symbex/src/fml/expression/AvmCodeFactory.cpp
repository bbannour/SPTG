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
	Operator * anOperator = anAvmCode->getOperator();

	AvmCode::this_container_type flattenArgs;
	BFCode arg;
	avm_size_t flatCount = 0;

	AvmCode::iterator it = anAvmCode->begin();
	AvmCode::iterator itEnd = anAvmCode->end();
	for( ; it != itEnd ; ++it )
	{
		if( (*it).is< AvmCode >() )
		{
			arg = AvmCodeFactory::flattenCode( (*it).bfCode() );

			if( anOperator->isWeakAssociative() &&
				arg->isOperator( anOperator ) )
			{
				flattenArgs.append( arg->getArgs() );

				++flatCount;
			}
			else
			{
				flattenArgs.append( arg );

				if( (*it).raw_pointer() != arg )
				{
					++flatCount;
				}
			}
		}
		else
		{
			flattenArgs.append( (*it) );
		}
	}

	if( flatCount > 0 )
	{
		if( anAvmCode->isUnique() )
		{
			anAvmCode->clear();
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
bool AvmCodeFactory::contains(ExecutableForm * anExecutable,
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
	else if( OperatorManager::isActivity(aCode->getOperator()) &&
			(aCode->empty() || (aCode->first() == ExecutableLib::MACHINE_SELF)) )
	{
		return( contains(anExecutable,
				anExecutable->getOnActivity( aCode->getAvmOpCode() ),
				anOpcode) );
	}
	else
	{
		AvmCode::const_iterator it = aCode->begin();
		AvmCode::const_iterator itEnd = aCode->end();
		for( ; it != itEnd ; ++it )
		{
			if( (*it).is< AvmCode >() )
			{
				if( contains(anExecutable, (*it).bfCode(), anOpcode) )
				{
					return true;
				}
			}
		}

		return( false );
	}
}


bool AvmCodeFactory::contains(ExecutableForm * anExecutable,
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
	else if( OperatorManager::isActivity(aCode->getOperator()) &&
			(aCode->empty() || (aCode->first() == ExecutableLib::MACHINE_SELF)) )
	{
		return( contains(anExecutable,
				anExecutable->getOnActivity( aCode->getAvmOpCode() ),
				anOpcode1, anOpcode2) );
	}
	else
	{
		AvmCode::const_iterator it = aCode->begin();
		AvmCode::const_iterator itEnd = aCode->end();
		for( ; it != itEnd ; ++it )
		{
			if( (*it).is< AvmCode >() )
			{
				if( contains(anExecutable, (*it).bfCode(), anOpcode1, anOpcode2) )
				{
					return true;
				}
			}
		}

		return false;
	}
}



} /* namespace sep */
