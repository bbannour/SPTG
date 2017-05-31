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

#include <collection/List.h>

#include <fml/workflow/WObject.h>

#include <fam/api/AbstractProcessorUnit.h>
#include <fam/api/ProcessorUnitAutoRegistration.h>
#include <fam/api/MainProcessorUnit.h>


#include <fam/api/ExtenderProcessorUnit.h>
#include <fam/api/MainProcessorUnit.h>

#include <fam/coverage/AvmCoverageProcessor.h>
#include <fam/coverage/FormulaCoverageFilter.h>
#include <fam/coverage/TransitionCoverageFilter.h>

#include <fam/debug/AvmDebugProcessor.h>

#include <fam/hitorjump/AvmHitOrJumpProcessor.h>

#include <fam/testing/OfflineTestProcessor.h>

#include <fam/queue/ExecutionQueue.h>

#include <fam/redundancy/RedundancyFilter.h>

#include <fam/serializer/GraphVizExecutionGraphSerializer.h>
#include <fam/serializer/GraphVizStatemachineSerializer.h>

#include <fam/trace/AvmTraceGenerator.h>


#include <sew/SymbexControllerUnitManager.h>

#include <util/avm_string.h>


namespace sep
{

////////////////////////////////////////////////////////////////////////////
// REGISTRY
////////////////////////////////////////////////////////////////////////////

typedef std::map< std::string ,
		IProcessorUnitRegistration * > MapOfProcessorFactory;


void ProcessorUnitRepository::toStreamKeys(
		OutStream & out, const std::string & header)
{
	out << TAB << header << "< keys: "
		<< getRepository().size() << " > {" << EOL;

	MapOfProcessorFactory::const_iterator itProc = getRepository().begin();
	MapOfProcessorFactory::const_iterator endProc = getRepository().end();
	for( ; itProc != endProc ; ++itProc )
	{
		out << TAB2 << (*itProc).first << EOL;
	}
	out << TAB << "}" << EOL_FLUSH;
}

void ProcessorUnitRepository::toStreamAll(
		OutStream & out, const std::string & header)
{
	out << TAB << header << "< keys: "
		<< getRepository().size() << " > {" << EOL;

	List< IProcessorUnitRegistration * > alreadyPrinted;

	MapOfProcessorFactory::const_iterator itProc = getRepository().begin();
	MapOfProcessorFactory::const_iterator endProc = getRepository().end();
	for( ; itProc != endProc ; ++itProc )
	{
		if( REGEX_STARTS( (*itProc).second->getTypeID() ,
				"(symbex|avm::processor)" ) )
		{
			if( not alreadyPrinted.contains( (*itProc).second ) )
			{
				alreadyPrinted.append( (*itProc).second );

				out << TAB2 << (*itProc).second->getTypeID() << EOL;
			}
		}
	}
	out << TAB << "}" << EOL_FLUSH;
}

void ProcessorUnitRepository::toStreamExported(
		OutStream & out, const std::string & header)
{
#define PROCESSOR_FACTORY_SHOW_TYPE_ID( Processor )  \
	out << TAB2 << Processor::AUTO_REGISTER_TOOL.getTypeID() << EOL;

	out << TAB1 << header << "< exported > {" << EOL;

	PROCESSOR_FACTORY_SHOW_TYPE_ID( MainProcessorUnit        )
	PROCESSOR_FACTORY_SHOW_TYPE_ID( ExecutionQueue           )
	PROCESSOR_FACTORY_SHOW_TYPE_ID( RedundancyFilter         )
	PROCESSOR_FACTORY_SHOW_TYPE_ID( AvmTraceGenerator        )

	PROCESSOR_FACTORY_SHOW_TYPE_ID( AvmDebugProcessor        )

	PROCESSOR_FACTORY_SHOW_TYPE_ID( AvmCoverageProcessor     )
	PROCESSOR_FACTORY_SHOW_TYPE_ID( FormulaCoverageFilter    )
	PROCESSOR_FACTORY_SHOW_TYPE_ID( TransitionCoverageFilter )

	PROCESSOR_FACTORY_SHOW_TYPE_ID( AvmHitOrJumpProcessor    )

	PROCESSOR_FACTORY_SHOW_TYPE_ID( OfflineTestProcessor     )

	PROCESSOR_FACTORY_SHOW_TYPE_ID( ExtenderProcessorUnit    )

//	PROCESSOR_FACTORY_SHOW_TYPE_ID( InputOutputFilter        )
//
//	PROCESSOR_FACTORY_SHOW_TYPE_ID( GraphSlicer              )
//
//	PROCESSOR_FACTORY_SHOW_TYPE_ID( AvmTraceDirector         )

	PROCESSOR_FACTORY_SHOW_TYPE_ID( GraphVizExecutionGraphSerializer )
	PROCESSOR_FACTORY_SHOW_TYPE_ID( GraphVizStatemachineSerializer   )

	out << TAB1 << "}" << EOL_FLUSH;
}


////////////////////////////////////////////////////////////////////////////////
// CREATION
////////////////////////////////////////////////////////////////////////////////

AbstractProcessorUnit * ProcessorUnitRepository::create(
		SymbexControllerUnitManager & aManager, WObject * wfProcessObject)
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

	if( aProcessorFactory != NULL )
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

	return( NULL );
}


} /* namespace sep */
