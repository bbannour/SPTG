/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 4 avr. 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmOperationVariable.h"

#include <fml/executable/BaseInstanceForm.h>

#include <fml/operator/OperatorManager.h>

#include <fml/infrastructure/Variable.h>


namespace sep
{


std::map< std::string , Operator * > AvmOperationVariable::theVariableMap;

std::map< std::string , Operator * > AvmOperationVariable::theContainerMap;

std::map< std::string , Operator * > AvmOperationVariable::theQueueMap;

std::map< std::string , Operator * > AvmOperationVariable::theTimeMap;

std::map< std::string , Operator * > AvmOperationVariable::theActivityMap;

std::map< std::string , Operator * > AvmOperationVariable::theOtherMap;




/**
 * LOADER
 */
void AvmOperationVariable::load()
{
	putVariable("newfresh"     , OperatorManager::OPERATOR_ASSIGN_NEWFRESH);
	putVariable("reset"        , OperatorManager::OPERATOR_ASSIGN_RESET);

	putVariable("changed"      , OperatorManager::OPERATOR_CHANGED);
	putVariable("changed_to"   , OperatorManager::OPERATOR_CHANGED_TO);


	putContainer("contains"    , OperatorManager::OPERATOR_CONTAINS);
	putContainer("in"          , OperatorManager::OPERATOR_IN);
	putContainer("notin"       , OperatorManager::OPERATOR_NOTIN);
	putContainer("subset"      , OperatorManager::OPERATOR_SUBSET);
	putContainer("subseteq"    , OperatorManager::OPERATOR_SUBSETEQ);
	putContainer("intersect"   , OperatorManager::OPERATOR_INTERSECT);

	putContainer("starts_with" , OperatorManager::OPERATOR_STARTS_WITH);
	putContainer("ends_with"   , OperatorManager::OPERATOR_ENDS_WITH);
	putContainer("concat"      , OperatorManager::OPERATOR_CONCAT);

	putContainer("empty"       , OperatorManager::OPERATOR_EMPTY);
	putContainer("nonempty"    , OperatorManager::OPERATOR_NONEMPTY);
	putContainer("singleton"   , OperatorManager::OPERATOR_SINGLETON);
	putContainer("populated"   , OperatorManager::OPERATOR_POPULATED);
	putContainer("full"        , OperatorManager::OPERATOR_FULL);
	putContainer("size"        , OperatorManager::OPERATOR_SIZE);

	putContainer("append"      , OperatorManager::OPERATOR_APPEND);
	putContainer("remove"      , OperatorManager::OPERATOR_REMOVE);

	putContainer("clear"       , OperatorManager::OPERATOR_CLEAR);
	putContainer("resize"      , OperatorManager::OPERATOR_RESIZE);

	putContainer("select"      , OperatorManager::OPERATOR_SELECT);

	putQueue("push"           , OperatorManager::OPERATOR_PUSH);
	putQueue("assign_top"     , OperatorManager::OPERATOR_ASSIGN_TOP);
	putQueue("top"            , OperatorManager::OPERATOR_TOP);
	putQueue("pop"            , OperatorManager::OPERATOR_POP);
	putQueue("pop_from"       , OperatorManager::OPERATOR_POP_FROM);
	putQueue("remove_popable" , OperatorManager::OPERATOR_REMOVE);

	putActivity("ienable"     , OperatorManager::OPERATOR_IENABLE_INVOKE);
	putActivity("enable"      , OperatorManager::OPERATOR_ENABLE_INVOKE);
	putActivity("enable#set"  , OperatorManager::OPERATOR_ENABLE_SET);

	putActivity("idisable"     , OperatorManager::OPERATOR_IDISABLE_INVOKE);
	putActivity("disable"      , OperatorManager::OPERATOR_DISABLE_INVOKE);
	putActivity("disable#set"  , OperatorManager::OPERATOR_DISABLE_SET);

	putActivity("iabort"       , OperatorManager::OPERATOR_IABORT_INVOKE);
	putActivity("abort"        , OperatorManager::OPERATOR_ABORT_INVOKE);
	putActivity("abort#set"    , OperatorManager::OPERATOR_ABORT_SET);
}


/**
 * DISPOSER
 */
void AvmOperationVariable::dispose()
{
	theVariableMap.clear();

	theContainerMap.clear();

	theQueueMap.clear();

	theTimeMap.clear();

	theActivityMap.clear();

	theOtherMap.clear();
}


/**
 * GETTER - SETTER
 */
Operator * AvmOperationVariable::get(const std::string & method)
{
	Operator * op = NULL;

	if( (op = getContainer(method)) != NULL )
	{
		return( op );
	}

	if( (op = getQueue(method)) != NULL )
	{
		return( op );
	}

	if( (op = getTime(method)) != NULL )
	{
		return( op );
	}

	if( (op = getActivity(method)) != NULL )
	{
		return( op );
	}

	if( (op = getVariable(method)) != NULL )
	{
		return( op );
	}

	return( getOther(method) );
}


Operator * AvmOperationVariable::get(const BF & aReceiver,
		const std::string & method)
{
	if( aReceiver.is< Variable >() )
	{
		return( get(aReceiver.to_ptr< Variable >(), method) );
	}
	else if( aReceiver.is< BaseInstanceForm >() )
	{
		return( get(aReceiver.to_ptr< BaseInstanceForm >(), method) );
	}
	return( get(method) );
}




Operator * AvmOperationVariable::get(
		Variable * aVariable, const std::string & method)
{
	if( (aVariable->hasTypeSpecifier() &&
		(aVariable->getTypeSpecifier()->hasTypeContainer() ||
		aVariable->getTypeSpecifier()->isTypedBuffer()     ||
		aVariable->getTypeSpecifier()->hasTypeContainer()  ||
		aVariable->getTypeSpecifier()->isTypedString() ) ) )
	{
		Operator * opContainer = getContainer(method);
		if( opContainer != NULL )
		{
			return( opContainer );
		}
	}

	if( aVariable->hasTypeSpecifier() &&
			aVariable->getTypeSpecifier()->hasTypeQueue() )
	{
		Operator * opQueue = getQueue(method);
		if( opQueue != NULL )
		{
			return( opQueue );
		}
	}

	if( aVariable->hasTypeSpecifier() &&
		(aVariable->getTypeSpecifier()->isTypedMachine()   ||
		aVariable->getTypeSpecifier()->weaklyTypedInteger() ) )
	{
		Operator * opActivity = getActivity(method);
		if( opActivity != NULL )
		{
			return( opActivity );
		}
	}

	if( aVariable->hasTypeSpecifier()
		&& aVariable->getTypeSpecifier()->hasTypedClockTime() )
	{
		Operator * opTime = getTime(method);
		if( opTime != NULL )
		{
			return( opTime );
		}
	}
	else
	{
		Operator * opVar = getVariable(method);
		if( opVar != NULL )
		{
			return( opVar );
		}
	}

	return( getOther(method) );
}


Operator * AvmOperationVariable::get(
		BaseInstanceForm * anInstance, const std::string & method)
{
	if( anInstance->hasTypeContainer()    ||
		anInstance->isTypedBuffer()       ||
		anInstance->isTypedString() )
	{
		Operator * opContainer = getContainer(method);
		if( opContainer != NULL )
		{
			return( opContainer );
		}
	}

	if( anInstance->hasTypeQueue() )
	{
		Operator * opQueue = getQueue(method);
		if( opQueue != NULL )
		{
			return( opQueue );
		}
	}

	if( anInstance->hasTypeSpecifier() && (
		anInstance->getTypeSpecifier()->isTypedMachine() ||
		anInstance->getTypeSpecifier()->weaklyTypedInteger() ) )
	{
		Operator * opActivity = getActivity(method);
		if( opActivity != NULL )
		{
			return( opActivity );
		}
	}

	if( anInstance->hasTypedClockTime() )
	{
		Operator * opTime = getTime(method);
		if( opTime != NULL )
		{
			return( opTime );
		}
	}
	else
	{
		Operator * opVar = getVariable(method);
		if( opVar != NULL )
		{
			return( opVar );
		}
	}

	return( getOther(method) );
}


Operator * AvmOperationVariable::get(
		BaseTypeSpecifier * aTypeSpecifier, const std::string & method)
{
	if( aTypeSpecifier->hasTypeContainer() ||
		aTypeSpecifier->isTypedBuffer()    ||
		aTypeSpecifier->isTypedString() )
	{
		Operator * opContainer = getContainer(method);
		if( opContainer != NULL )
		{
			return( opContainer );
		}
	}

	if( aTypeSpecifier->hasTypeQueue() )
	{
		Operator * opQueue = getQueue(method);
		if( opQueue != NULL )
		{
			return( opQueue );
		}
	}

	if( aTypeSpecifier->isTypedMachine() ||
		aTypeSpecifier->weaklyTypedInteger() )
	{
		Operator * opActivity = getActivity(method);
		if( opActivity != NULL )
		{
			return( opActivity );
		}
	}

	if( aTypeSpecifier->hasTypedTime() )
	{
		Operator * opTime = getTime(method);
		if( opTime != NULL )
		{
			return( opTime );
		}
	}
	else
	{
		Operator * opVar = getVariable(method);
		if( opVar != NULL )
		{
			return( opVar );
		}
	}

	return( getOther(method) );
}


bool AvmOperationVariable::exist(BaseInstanceForm * anInstance,
			const std::string & method)
{
	if( (anInstance->hasTypeContainer() || anInstance->isTypedBuffer()) &&
		isContainer(method) )
	{
		return( true );
	}

	if( anInstance->hasTypeQueue() && isQueue(method) )
	{
		return( true );
	}

	if( isActivity(method) && anInstance->hasTypeSpecifier() && (
		anInstance->getTypeSpecifier()->isTypedMachine() ||
		anInstance->getTypeSpecifier()->weaklyTypedInteger() ) )
	{
		return( true );
	}

	if( isVariable(method) )
	{
		return( true );
	}

	return( isOther(method) );
}



void AvmOperationVariable::put(BaseInstanceForm * anInstance,
		const std::string & method, Operator * anOperator)
{
	if( anInstance->hasTypedClockTime() )
	{
		putTime(method, anOperator);
	}
	else if( anInstance->hasTypeQueue() )
	{
		putQueue(method, anOperator);
	}
	else if( anInstance->hasTypeContainer()     ||
			anInstance->isTypedBuffer()    )
	{
		putContainer(method, anOperator);
	}
	else if( anInstance->hasTypeSpecifier() && (
			anInstance->getTypeSpecifier()->isTypedMachine() ||
			anInstance->getTypeSpecifier()->weaklyTypedInteger() ) )
	{
		putActivity(method, anOperator);
	}

	putOther(method, anOperator);
}



} /* namespace sep */
