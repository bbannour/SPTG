/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 29 nov. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "ProcessorUnitFactory.h"

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <fam/api/AbstractProcessorUnit.h>
#include <fam/api/ProcessorUnitRepository.h>

#include <fam/debug/AvmDebugProcessor.h>

#include <sew/Workflow.h>
#include <sew/SymbexControllerUnitManager.h>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
// CREATION
////////////////////////////////////////////////////////////////////////////////

AbstractProcessorUnit * ProcessorUnitFactory::create(
		SymbexControllerUnitManager & aManager, WObject * wfProcessObject)
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( wfProcessObject )
			<< "Unexpected a <null> processor unit parameter WObject !!!"
			<< SEND_EXIT;

	return( ProcessorUnitRepository::create(aManager, wfProcessObject) );
}


bool ProcessorUnitFactory::createList(
		SymbexControllerUnitManager & aManager,
		List< WObject * > & listOfProcessWObject)
{
	List< WObject * >::iterator it = listOfProcessWObject.begin();
	List< WObject * >::iterator endIt = listOfProcessWObject.end();
	for( ; it != endIt ; ++it )
	{
		AbstractProcessorUnit * tmpProcessor = create(aManager, (*it));

		if( tmpProcessor != NULL )
		{
			aManager.append( tmpProcessor );
		}
		else
		{
			AVM_OS_ERROR_ALERT << "ProcessorUnitFactory::create:> "
						"Unregistered Processor WObject Type ?" << std::endl
					<< str_header( *it )
					<< SEND_ALERT;

			AVM_OS_WARN << incr_stream( *it );

			return( false );
		}
	}

	return true;
}


////////////////////////////////////////////////////////////////////////////////
// CONFIGURE  API
////////////////////////////////////////////////////////////////////////////////

bool ProcessorUnitFactory::configure(
		SymbexControllerUnitManager & aPluginProcessorManager,
		WObject * wfDirectorObject, WObject * moeProfile)
{
	/////////////////////////////////////
	// PROCESSORS CREATION
	/////////////////////////////////////

	// section worker / PROCESSOR
	List< WObject * > listOfProcessWObject;
	Query::getRegexWObjectInSequence(wfDirectorObject,
			Workflow::SECTION_FAM_CONTAINERS_REGEX_ID, listOfProcessWObject);

	if( not createList(aPluginProcessorManager, listOfProcessWObject) )
	{
		return( false );
	}


	/////////////////////////////////////
	// WORKFLOW SCHEDULER INITIALIZATION
	/////////////////////////////////////

	if( not configureProcessorScheduler(AVM_PRE_PROCESSING_STAGE,
			aPluginProcessorManager.getPreprocessor(),
			Query::getRegexWPropertyValue(moeProfile,
					CONS_WID2("pre", "process"), BF::REF_NULL)) )
	{
		AVM_OS_ERROR_ALERT
				<< "PreProcessorManager:> Configure preprocessor Failed !!!"
				<< SEND_ALERT;

		return( false );
	}

	if( not configureProcessorScheduler(AVM_PRE_FILTERING_STAGE,
			aPluginProcessorManager.getPrefilter(),
			Query::getRegexWPropertyValue(moeProfile,
					CONS_WID2("pre", "filter"), BF::REF_NULL)) )
	{
		AVM_OS_ERROR_ALERT << "ProcessorUnitFactory::configure:> "
					"Configure prefilter Failed !!!"
				<< SEND_ALERT;

		return( false );
	}

	if( not configureProcessorScheduler(AVM_POST_FILTERING_STAGE,
			aPluginProcessorManager.getPostfilter(),
			Query::getRegexWPropertyValue(moeProfile,
					CONS_WID2("post", "filter"), BF::REF_NULL)) )
	{
		AVM_OS_ERROR_ALERT << "ProcessorUnitFactory::configure:> "
					"Configure postfilter Failed !!!"
				<< SEND_ALERT;

		return( false );
	}

	if( not configureProcessorScheduler(AVM_POST_PROCESSING_STAGE,
			aPluginProcessorManager.getPostprocessor(),
			Query::getRegexWPropertyValue(moeProfile,
					CONS_WID2("post", "process"), BF::REF_NULL)) )
	{
		AVM_OS_ERROR_ALERT << "ProcessorUnitFactory::configure:> "
					"Configure postprocessor Failed !!!"
				<< SEND_ALERT;

		return( false );
	}


	/////////////////////////////////////
	// PROCESSORS CONFIGURE
	/////////////////////////////////////

	if( not aPluginProcessorManager.configureControllerUnits() )
	{
		AVM_OS_WARN << "ProcessorUnitFactory::configure:> Failed !!!"
				<< std::endl;

		return( false );
	}

/*
 * NEW CONSISE SYNTAX
supervisor {
	limit 'of graph exploration' [
		eval = 10
		...
	]
	queue 'for graph exploration' [
		strategy = 'BFS'
		...
	]
	console [
		format = "\nstep:%1% , context:%2% , height:%3% , width:%4%"
		...
	]
}
*/
	/////////////////////////////////////
	// MAIN PROCESSOR CONFIGURE
	/////////////////////////////////////

	MainProcessorUnit & theMainProcessor =
			aPluginProcessorManager.getMainProcessor();

	if( not theMainProcessor.hasParameterWObject() )
	{
		theMainProcessor.setParameterWObject(
				Query::getRegisterWObject(wfDirectorObject,
						MainProcessorUnit::AUTO_REGISTER_TOOL) );
	}

	if( not theMainProcessor.configure() )
	{
		AVM_OS_WARN << "ProcessorUnitFactory::configure:> Failed to "
			"configure the default stop processor << "
			<< theMainProcessor.getParameterWObject()->getFullyQualifiedNameID()
			<< " >> " << std::endl;

		return( false );
	}


	/////////////////////////////////////
	// QUEUE PROCESSOR CONFIGURE
	/////////////////////////////////////

	ExecutionQueue & theQueueProcessor =
			aPluginProcessorManager.getExecutionQueue();

	WObject * queueWObject = Query::getRegexWObjectByNameID(
			theMainProcessor.getParameterWObject(),
			Workflow::SECTION_FAM_QUEUE_REGEX_ID, WObject::_NULL_);

	if( queueWObject != WObject::_NULL_ )
	{
		queueWObject = theMainProcessor.getParameterWObject();
	}
	else
	{
		queueWObject = Query::getWPropertyWReference(
				theMainProcessor.getParameterWObject(),
				"queue", WObject::_NULL_);
		if( queueWObject == WObject::_NULL_ )
		{
			//!! DEPRECATED
			queueWObject = Query::getWPropertyWReference(
					moeProfile, "queue", WObject::_NULL_);
			if( queueWObject == WObject::_NULL_ )
			{
				queueWObject = Query::getRegisterWObject(moeProfile,
						ExecutionQueue::AUTO_REGISTER_TOOL);
			}
		}
	}

	if( queueWObject != WObject::_NULL_ )
	{
		theQueueProcessor.setParameterWObject( queueWObject );
	}

	if( theQueueProcessor.hasParameterWObject() )
	{
		if( not theQueueProcessor.configureImpl() )
		{
			AVM_OS_WARN << "ProcessorUnitFactory::configure:> Failed to "
					"configure the default queue processor << "
					<< theQueueProcessor
						.getParameterWObject()->getFullyQualifiedNameID()
					<< " >> " << std::endl;

			return( false );
		}
	}
	else
	{
		AVM_OS_WARN << "ProcessorUnitFactory::configure:> Failed to "
				"configure the default queue processor with a null wfObject !"
				<< std::endl;

		return( false );
	}


	/////////////////////////////////////
	// REDUNDANCY PROCESSOR CONFIGURE
	/////////////////////////////////////

	RedundancyFilter & theRedundancyProcessor =
			aPluginProcessorManager.getRedundancyProcessor();

	if( not theRedundancyProcessor.hasParameterWObject() )
	{
		theRedundancyProcessor.setParameterWObject(
				theMainProcessor.getParameterWObject() );
	}

	if( not theRedundancyProcessor.configureImpl() )
	{
		AVM_OS_WARN << "ProcessorUnitFactory::configure:> Failed to "
				"configure the default redundancy processor << "
				<< theRedundancyProcessor
					.getParameterWObject()->getFullyQualifiedNameID()
				<< " >> " << std::endl;

		return( false );
	}

AVM_IF_DEBUG_ENABLED_AND( aPluginProcessorManager.isAutoConfigure() )
	AVM_OS_LOG << "ProcessorUnitFactory::autoconfigure <"
			<< aPluginProcessorManager.strUniqId() << ">" << std::endl;
	aPluginProcessorManager.toStream( AVM_OS_LOG );
AVM_ENDIF_DEBUG_FLAG_AND( CONFIGURING )

	return true;
}


bool ProcessorUnitFactory::configureProcessorScheduler(
		avm_computing_process_stage_t aRequirement,
		CompositeControllerUnit & processorScheduler, const BF & aScheduler)
{
	if( aScheduler.valid() )
	{
		AbstractProcessorUnit * aProcessor = NULL;

		if( WObjectManager::is( aScheduler ) )
		{
			aProcessor = processorScheduler.getControllerUnitManager().
					getControllerUnit( WObjectManager::from( aScheduler ) );

			if( aProcessor != NULL )
			{
				aProcessor->enablePlugin(aRequirement);

				processorScheduler.append( aProcessor );
			}
			else
			{
				AVM_OS_ERROR_ALERT
						<< "configurePostprocess:> UnFound WObject << "
						<< WObjectManager::from( aScheduler )->strUniqId()
						<< " >> Processor using as processor !!!"
						<< SEND_ALERT;

				return( false );
			}
		}
		else if( aScheduler.is< AvmCode >() )
		{
			AvmCode * aCode = aScheduler.to_ptr< AvmCode >();

			AvmCode::iterator it = aCode->begin();
			for( ; it != aCode->end() ; ++it )
			{
				configureProcessorScheduler(
						aRequirement, processorScheduler, (*it));
			}
		}
		else
		{
			aProcessor = processorScheduler.getControllerUnitManager().
					getControllerUnit( aScheduler.str() );

			if( aProcessor != NULL )
			{
				aProcessor->enablePlugin(aRequirement);

				processorScheduler.append( aProcessor );
			}
			else
			{
				AVM_OS_ERROR_ALERT
						<< "configurePostprocess:> UnFound WObject << "
						<< WObjectManager::from( aScheduler )->strUniqId()
						<< " >> Processor using as processor !!!"
						<< SEND_ALERT;

				return( false );
			}
		}
	}

	return( true );
}



} /* namespace sep */
