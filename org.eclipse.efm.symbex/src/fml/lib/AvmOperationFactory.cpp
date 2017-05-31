/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 5 avr. 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmOperationFactory.h"

#include <fml/executable/BaseInstanceForm.h>
#include <fml/executable/InstanceOfData.h>
#include <fml/executable/InstanceOfMachine.h>

#include <fml/expression/BuiltinContainer.h>

#include <fml/lib/AvmOperationExpression.h>
#include <fml/lib/AvmOperationMachine.h>
#include <fml/lib/AvmOperationVariable.h>

#include <fml/operator/OperatorManager.h>

#include <fml/runtime/RuntimeID.h>

#include <fml/type/BaseTypeSpecifier.h>

#include <fml/infrastructure/Machine.h>
#include <fml/infrastructure/Variable.h>


namespace sep
{


std::map< std::string , Operator * > AvmOperationFactory::theGlobalMap;


/**
 * LOADER
 */
void AvmOperationFactory::load()
{
	AvmOperationExpression::load();

	AvmOperationMachine::load();

	AvmOperationVariable::load();
}


/**
 * DISPOSER
 */
void AvmOperationFactory::dispose()
{
	AvmOperationVariable::dispose();

	AvmOperationMachine::dispose();

	AvmOperationExpression::dispose();

	theGlobalMap.clear();
}



/**
 * GETTER - SETTER
 */
Operator * AvmOperationFactory::get(const std::string & method)
{
	Operator * op = NULL;

	if( (op = getGlobal(method)) != NULL )
	{
		return( op );
	}

	if( (op = AvmOperationVariable::get(method)) != NULL )
	{
		return( op );
	}

	if( (op = AvmOperationMachine::get(method)) != NULL )
	{
		return( op );
	}

	return( AvmOperationExpression::get(method) );
}


Operator * AvmOperationFactory::get(const BF & aReceiver,
		const std::string & method)
{
	if( aReceiver.is< BaseInstanceForm >() )
	{
		return( get(aReceiver.to_ptr< BaseInstanceForm >(), method) );
	}
	else if( aReceiver.is< Machine >() ||
			aReceiver.is< InstanceOfMachine >() ||
			aReceiver.is< RuntimeID >() )
	{
		return( AvmOperationMachine::get(method) );
	}

	else if( aReceiver.is< Variable >() )
	{
		Variable * aVar = aReceiver.to_ptr< Variable >();

		if( aVar->hasTypeSpecifier() )
		{
			BaseTypeSpecifier * varTS = aVar->getTypeSpecifier();
			if( varTS->isTypedMachine() )
			{
				Operator * opVar = AvmOperationMachine::get(method);
				if( opVar != NULL )
				{
					return( opVar );
				}
			}

			Operator * opVar = AvmOperationVariable::get(varTS, method);
			if( opVar != NULL )
			{
				return( opVar );
			}
		}
	}

	else if( aReceiver.is< InstanceOfData >() )
	{
		InstanceOfData * aData = aReceiver.to_ptr< InstanceOfData >();

		if( aData->hasTypeSpecifier() )
		{
			BaseTypeSpecifier * varTS = aData->getTypeSpecifier();
			if( varTS->isTypedMachine() )
			{
				return( AvmOperationMachine::get(method) );
			}
			else
			{
				Operator * opVar = AvmOperationVariable::get(varTS, method);
				if( opVar != NULL )
				{
					return( opVar );
				}
			}
		}
	}

	else if( aReceiver.is< BuiltinCollection >() ||
			aReceiver.is< String >() )
	{
		return( AvmOperationVariable::get(method) );
	}
	else
	{
		Operator * opExpr = AvmOperationExpression::get(aReceiver, method);
		if( opExpr != NULL )
		{
			return( opExpr );
		}
	}

	return( get(method) );
}

Operator * AvmOperationFactory::get(
		BaseInstanceForm * anInstance, const std::string & method)
{
	if( anInstance->isTypedMachine() || anInstance->is< InstanceOfMachine >() )
	{
		return( AvmOperationMachine::get(anInstance, method) );
	}
	else
	{
		Operator * opVar = AvmOperationVariable::get(anInstance, method);
		if( opVar != NULL )
		{
			return( opVar );
		}

		return( getGlobal(method) );
	}
}



bool AvmOperationFactory::exist(const std::string & method)
{
	return( isGlobal(method) ||
			AvmOperationVariable::exist(method) ||
			AvmOperationMachine::exist(method) ||
			AvmOperationExpression::exist(method) );
}


bool AvmOperationFactory::exist(BaseInstanceForm * anInstance,
		const std::string & method)
{
	return( AvmOperationVariable::exist(anInstance, method) ||
			AvmOperationMachine::exist(anInstance, method)  ||
			isGlobal(method) );
}


bool AvmOperationFactory::exist(const std::string & method, Operator * anOperator)
{
	return( (anOperator == getGlobal(method))                 ||
			AvmOperationVariable::exist(method, anOperator)   ||
			AvmOperationMachine::exist(method, anOperator)    ||
			AvmOperationExpression::exist(method, anOperator) );
}



void AvmOperationFactory::put(const std::string & method, Operator * anOperator)
{
	if( exist(method, anOperator) )
	{
		return;
	}
	putGlobal(method, anOperator);
}


void AvmOperationFactory::put(BaseInstanceForm * anInstance,
		const std::string & method, Operator * anOperator)
{
	putGlobal(method, anOperator);
}



} /* namespace sep */
