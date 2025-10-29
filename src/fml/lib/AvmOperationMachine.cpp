/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 3 avr. 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmOperationMachine.h"

#include <fml/executable/BaseInstanceForm.h>

#include <fml/operator/OperatorManager.h>

#include <fml/infrastructure/Machine.h>


namespace sep
{


std::map< std::string , const Operator * > AvmOperationMachine::theActivityMap;

std::map< std::string , const Operator * > AvmOperationMachine::theStatusMap;

std::map< std::string , const Operator * > AvmOperationMachine::theOtherMap;



/**
 * LOADER
 */
void AvmOperationMachine::load()
{
	putActivity("init"         , OperatorManager::OPERATOR_INIT);
	putActivity("final"        , OperatorManager::OPERATOR_FINAL);
	putActivity("destroy"      , OperatorManager::OPERATOR_DESTROY);

	putActivity("start"        , OperatorManager::OPERATOR_START);
	putActivity("restart"      , OperatorManager::OPERATOR_RESTART);
	putActivity("stop"         , OperatorManager::OPERATOR_STOP);


	putActivity("ienable"      , OperatorManager::OPERATOR_IENABLE_INVOKE);
	putActivity("enable"       , OperatorManager::OPERATOR_ENABLE_INVOKE);
	putActivity("enable#set"   , OperatorManager::OPERATOR_ENABLE_SET);


	putActivity("idisable"     , OperatorManager::OPERATOR_IDISABLE_INVOKE);
	putActivity("disable"      , OperatorManager::OPERATOR_DISABLE_INVOKE);
	putActivity("disable#set"  , OperatorManager::OPERATOR_DISABLE_SET);

	putActivity("disable#child"  , OperatorManager::OPERATOR_DISABLE_CHILD);
	putActivity("disable#selves" , OperatorManager::OPERATOR_DISABLE_SELVES);


	putActivity("iabort"       , OperatorManager::OPERATOR_IABORT_INVOKE);
	putActivity("abort"        , OperatorManager::OPERATOR_ABORT_INVOKE);
	putActivity("abort#set"    , OperatorManager::OPERATOR_ABORT_SET);

	putActivity("abort#child"  , OperatorManager::OPERATOR_ABORT_CHILD);
	putActivity("abort#selves" , OperatorManager::OPERATOR_ABORT_SELVES);


	putActivity("irun"         , OperatorManager::OPERATOR_IRUN);
	putActivity("run"          , OperatorManager::OPERATOR_RUN);
	putActivity("rtc"          , OperatorManager::OPERATOR_RTC);

	putActivity("schedule"     , OperatorManager::OPERATOR_SCHEDULE_INVOKE);
	putActivity("schedule#run" , OperatorManager::OPERATOR_SCHEDULE_INVOKE);
	putActivity("schedule#get" , OperatorManager::OPERATOR_SCHEDULE_GET);
	putActivity("schedule#in"  , OperatorManager::OPERATOR_SCHEDULE_IN);
	putActivity("schedule#set" , OperatorManager::OPERATOR_SCHEDULE_SET);

	putActivity("defer"        , OperatorManager::OPERATOR_DEFER_INVOKE);
	putActivity("defer#run"    , OperatorManager::OPERATOR_DEFER_INVOKE);
	putActivity("defer#get"    , OperatorManager::OPERATOR_DEFER_GET);
	putActivity("defer#set"    , OperatorManager::OPERATOR_DEFER_SET);

	putActivity("suspend"      , OperatorManager::OPERATOR_SUSPEND);
	putActivity("resume"       , OperatorManager::OPERATOR_RESUME);
	putActivity("wait"         , OperatorManager::OPERATOR_WAIT);


	putStatus("status_was"     , OperatorManager::OPERATOR_STATUS_WAS);
	putStatus("status_is"      , OperatorManager::OPERATOR_STATUS_IS);
	putStatus("status_being"   , OperatorManager::OPERATOR_STATUS_BEING);
	putStatus("status_will"    , OperatorManager::OPERATOR_STATUS_WILL);

	putStatus("changed"        , OperatorManager::OPERATOR_CHANGED);
	putStatus("changed_to"     , OperatorManager::OPERATOR_CHANGED_TO);
}


/**
 * DISPOSER
 */
void AvmOperationMachine::dispose()
{
	theActivityMap.clear();

	theStatusMap.clear();

	theOtherMap.clear();
}



/**
 * GETTER - SETTER
 */
const Operator * AvmOperationMachine::get(const std::string & method)
{
	const Operator * op = nullptr;

	if( (op = getActivity(method)) != nullptr )
	{
		return( op );
	}

	if( (op = getStatus(method)) != nullptr )
	{
		return( op );
	}

	return( getOther(method) );
}


const Operator * AvmOperationMachine::get(const BF & aReceiver,
		const std::string & method)
{
	if( aReceiver.is_exactly< Machine >() )
	{
		return( get(aReceiver.to_ptr< Machine >(), method) );
	}
	else if( aReceiver.is< BaseInstanceForm >() )
	{
		return( get(aReceiver.to_ptr< BaseInstanceForm >(), method) );
	}
	return( get(method) );
}



} /* namespace sep */
