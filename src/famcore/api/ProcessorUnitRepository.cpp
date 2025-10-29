/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 4 déc. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "ProcessorUnitRepository.h"

#include <util/avm_string.h>

#include <collection/List.h>

#include <fml/workflow/WObject.h>

#include  <famcore/api/AbstractProcessorUnit.h>
#include  <famcore/api/ProcessorUnitAutoRegistration.h>
#include  <famcore/api/MainProcessorUnit.h>

#include  <famcore/debug/AvmDebugProcessor.h>

#include  <famcore/queue/ExecutionQueue.h>

#include  <famcore/redundancy/RedundancyFilter.h>

#include <sew/SymbexControllerUnitManager.h>


namespace sep
{

////////////////////////////////////////////////////////////////////////////
// REGISTRY
////////////////////////////////////////////////////////////////////////////

typedef std::map< std::string ,
		IProcessorUnitRegistration * > MapOfProcessorFactory;


IProcessorUnitRegistration * ProcessorUnitRepository::getProcessorFactory(
		const std::string & aTypeID)
{
	auto aProcessorFactory = getRepository()[ aTypeID ];
	if( aProcessorFactory == nullptr )
	{
		for( auto itMap : getRepository() )
		{
			if( REGEX_MATCH(aTypeID , itMap.first) )
			{
				aProcessorFactory = itMap.second;
				if( aProcessorFactory != nullptr )
				{
					break;
				}
			}
		}
	}

	return( aProcessorFactory );
}

// All FAM_ID of all FAM, with maybe more than one FAM_ID for a FAM
// A FAM has a main FAM_ID and up to 3 aliases ID
std::vector<std::string> ProcessorUnitRepository::getAllAvailableFamID()
{
	std::vector< std::string> allAvailableFamID;

	for( auto itMap : getRepository() )
	{
		allAvailableFamID.push_back(itMap.first);
	}

	return allAvailableFamID;
}

// One and only one FAM_ID, his main ID, of all FAM
std::vector<std::string> ProcessorUnitRepository::getAvailableFamID()
{
	std::vector< std::string> allAvailableFamID;

	for( auto itMap : getRepository() )
	{
		allAvailableFamID.push_back(itMap.second->getTypeID());
	}

	return allAvailableFamID;
}



void ProcessorUnitRepository::toStreamKeys(
		OutStream & out, const std::string & header)
{
	out << TAB << header << "< keys: "
		<< getRepository().size() << " > {" << EOL;

	for( const auto & itProc : getRepository() )
	{
		out << TAB2 << itProc.first << EOL;
	}
	out << TAB << "}" << EOL_FLUSH;
}

void ProcessorUnitRepository::toStreamAll(
		OutStream & out, const std::string & header)
{
	out << TAB << header << "< keys: "
		<< getRepository().size() << " > {" << EOL;

	List< IProcessorUnitRegistration * > alreadyPrinted;

	for( const auto & itProc : getRepository() )
	{
		if( REGEX_STARTS( itProc.second->getTypeID() ,
				"(symbex|avm::processor)" ) )
		{
			if( not alreadyPrinted.contains( itProc.second ) )
			{
				alreadyPrinted.append( itProc.second );

				out << TAB2 << itProc.second->getTypeID() << EOL;
			}
		}
	}
	out << TAB << "}" << EOL_FLUSH;
}


////////////////////////////////////////////////////////////////////////////////
// CREATION
////////////////////////////////////////////////////////////////////////////////

AbstractProcessorUnit * ProcessorUnitRepository::create(
		SymbexControllerUnitManager & aManager, const WObject * wfProcessObject)
{
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( not getRepository().empty() )
			<< "Unexpected an empty processor unit repository !!!"
			<< SEND_EXIT;

	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( wfProcessObject )
			"processor unit parameter WObject !!!"
			<< SEND_EXIT;

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , CONFIGURING )
	AVM_OS_COUT << "Processor Type:> "
			<< wfProcessObject->getQualifiedTypeNameID() << EOL_FLUSH;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , CONFIGURING )


	IProcessorUnitRegistration * aProcessorFactory = ProcessorUnitRepository::
			getProcessorFactory( wfProcessObject->getQualifiedTypeNameID() );

	if( aProcessorFactory != nullptr )
	{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , CONFIGURING )
	AVM_OS_COUT << "    ==> found :> "
			<< aProcessorFactory->getTypeID() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , CONFIGURING )

		// Case of Main processor Factory
		if( &(MainProcessorUnit::AUTO_REGISTER_TOOL) == aProcessorFactory )
		{
			if( aManager.getMainProcessor().hasParameterWObject() )
			{
				return( new MainProcessorUnit(aManager, wfProcessObject) );
			}
			else
			{
				aManager.getMainProcessor().
						setParameterWObject(wfProcessObject);

				return( &( aManager.getMainProcessor() ) );
			}
		}
		else if( &(ExecutionQueue::AUTO_REGISTER_TOOL) == aProcessorFactory )
		{
			if( not aManager.getExecutionQueue().hasParameterWObject() )
			{
				aManager.getExecutionQueue().
						setParameterWObject(wfProcessObject);
			}

			return( &( aManager.getExecutionQueue() ) );
		}
		else if( &(RedundancyFilter::AUTO_REGISTER_TOOL) == aProcessorFactory )
		{
			if( not aManager.getRedundancyProcessor().hasParameterWObject() )
			{
				aManager.getRedundancyProcessor().
						setParameterWObject(wfProcessObject);
			}

			return( &( aManager.getExecutionQueue() ) );
		}


//		else if( &(AvmDebugProcessor::AUTO_REGISTER_TOOL) == aProcessorFactory )
//		{
//			if( aManager.getDebugProcessor().hasParameterWObject() )
//			{
//				return( new AvmDebugProcessor(aManager, wfProcessObject) );
//			}
//			else
//			{
//				aManager.getDebugProcessor().setParameterWObject(wfProcessObject);
//
//				return( &( aManager.getDebugProcessor() ) );
//			}
//		}


		return( aProcessorFactory->newInstance( aManager , wfProcessObject ) );
	}
	else
	{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , CONFIGURING )
	AVM_OS_COUT << "    ==> Unfound in Reppsitory of "
		<< getRepository().size() << " elements" << std::endl;
	toStreamKeys(AVM_OS_COUT);
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , CONFIGURING )
	}

	return( nullptr );
}


} /* namespace sep */
