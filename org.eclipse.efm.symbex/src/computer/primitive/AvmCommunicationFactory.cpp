/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 27 oct. 2010
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmCommunicationFactory.h"

#include <fml/common/ModifierElement.h>

#include <computer/EvaluationEnvironment.h>
#include <computer/ExecutionDataFactory.h>
#include <computer/ExecutionEnvironment.h>

#include <computer/instruction/InstructionEnvironment.h>

#include <fml/buffer/BaseBufferForm.h>
#include <fml/buffer/BroadcastBuffer.h>

#include <fml/executable/ExecutableLib.h>
#include <fml/executable/InstanceOfBuffer.h>
#include <fml/executable/InstanceOfConnect.h>
#include <fml/executable/InstanceOfData.h>
#include <fml/executable/InstanceOfMachine.h>
#include <fml/executable/InstanceOfPort.h>
#include <fml/executable/Router.h>
#include <fml/executable/RoutingData.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/StatementConstructor.h>

#include <fml/infrastructure/ComProtocol.h>

#include <fml/operator/OperatorManager.h>

#include <fml/runtime/ExecutionConfiguration.h>
#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/ExecutionSynchronizationPoint.h>
#include <fml/runtime/Message.h>
#include <fml/runtime/RuntimeLib.h>
#include <fml/runtime/RuntimeID.h>

#include <fml/workflow/UniFormIdentifier.h>


namespace sep
{


/**
 * SEARCH ROUTING DATA
 */
const RoutingData & AvmCommunicationFactory::searchInputRoutingData(
		const ExecutionData & anED, InstanceOfPort  * aPort,
		RuntimeID & aRoutingRID)
{
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( aPort->getModifier().hasDirectionInput() )
			<< "AvmCommunicationFactory::searchInputRoutingData :> "
				"Unexpected non-INPUT port "
			<< aPort->getFullyQualifiedNameID() << " !!!"
			<< SEND_EXIT;

	if( aPort->hasInputRoutingData() )
	{
		aRoutingRID = aPort->getInputRoutingData().getRuntimeRID();

		return( aPort->getInputRoutingData() );
	}
	else if( aPort->isPort() )
	{
		if( aPort->hasRuntimeContainerRID() )
		{
			aRoutingRID = aPort->getRuntimeContainerRID();
		}
		else if( aRoutingRID.valid() )
		{
			aRoutingRID = aRoutingRID.getCommunicator(aPort);
		}
	}
	else if( aPort->isSignal() )
	{
		while( aRoutingRID.valid()
			&& (not anED.getRuntime(aRoutingRID).hasRouter()) )
		{
			aRoutingRID = aRoutingRID.getPRID();
		}
	}

	if( aRoutingRID.valid() )
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT(
			anED.getRuntime(aRoutingRID).hasRouter() )
				<< "Searching Input RoutingData message error : << "
				<< aRoutingRID.getFullyQualifiedNameID()
				<< " >> doesn't have router !!!"
				<< SEND_EXIT;


		const RoutingData & aRoutingData = anED.getRuntime(aRoutingRID).
				getRouter().getInputRouting( aPort->getRouteOffset() );
		if( aRoutingData != NULL )
		{
//			aRoutingRID = ( aPort->isVisibilityPublic() )?
//					aRoutingRID.getPRID() : aRoutingRID;
			aRoutingRID = aRoutingRID.getCommunicator(
					aRoutingData.getMachine() );
		}

		return( aRoutingData );
	}

	return( RoutingData::_NULL_ );
}


const RoutingData & AvmCommunicationFactory::searchOutputRoutingData(
		const ExecutionData & anED, InstanceOfPort  * aPort,
		RuntimeID & aRoutingRID)
{
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( aPort->getModifier().hasDirectionOutput() )
			<< "AvmCommunicationFactory::searchOutputRoutingData :> "
				"Unexpected non-OUTPUT port "
			<< aPort->getFullyQualifiedNameID() << " !!!"
			<< SEND_EXIT;

	if( aPort->hasOutputRoutingData() )
	{
		aRoutingRID = aPort->getOutputRoutingData().getRuntimeRID();
		return( aPort->getOutputRoutingData() );
	}
	else if( aPort->isPort() )
	{
		if( aPort->hasRuntimeContainerRID() )
		{
			aRoutingRID = aPort->getRuntimeContainerRID();
		}
		else if( aRoutingRID.valid() )
		{
			aRoutingRID = aRoutingRID.getCommunicator(aPort);
		}
	}
	else if( aPort->isSignal() )
	{
		while( aRoutingRID.valid()
			&& (not anED.getRuntime(aRoutingRID).hasRouter()) )
		{
			aRoutingRID = aRoutingRID.getPRID();
		}
	}

	if( aRoutingRID.valid() )
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT(
			anED.getRuntime(aRoutingRID).hasRouter() )
				<< "Searching Output RoutingData message error : << "
				<< aRoutingRID.getFullyQualifiedNameID()
				<< " >> doesn't have router !!!"
				<< SEND_EXIT;


		const RoutingData & aRoutingData = anED.getRuntime(aRoutingRID).
				getRouter().getOutputRouting( aPort->getRouteOffset() );
		if( aRoutingData != NULL )
		{
//			aRoutingRID = ( aPort->isVisibilityPublic() )?
//					aRoutingRID.getPRID() : aRoutingRID;
			aRoutingRID = aRoutingRID.getCommunicator(
					aRoutingData.getMachine() );
		}

		return( aRoutingData );
	}

	return( RoutingData::_NULL_ );
}


/*
 * CHECK ROUTING INFORMATION
 */
bool AvmCommunicationFactory::isRoutingProtocolEnv(
		COMPILE_CONTEXT * aCTX, InstanceOfPort * aPort)
{
	return( false );
}

bool AvmCommunicationFactory::isRoutingProtocolRdv(
		COMPILE_CONTEXT * aCTX, InstanceOfPort * aPort)
{
	return( false );
}


/*
 * POP MESSAGE
 */
bool AvmCommunicationFactory::popMessage(
		ExecutionEnvironment & ENV, InstanceOfPort * aPort)
{
	RuntimeID aRoutingRID = ENV.mARG->outED->mRID;

	const RoutingData & aRoutingData =
			searchInputRoutingData(ENV.mARG->outED, aPort, aRoutingRID);

	if( aRoutingData != NULL )
	{
		switch( aRoutingData.getProtocol() )
		{
			case ComProtocol::PROTOCOL_ENVIRONMENT_KIND:
			{
				if( ENV.mARG->outED->getRuntime(aRoutingRID).
						isEnvironmentEnabledCommunication() )
				{
					return( popMessage_environment(ENV, aRoutingRID, aRoutingData) );
				}
				return( false );
			}

			case ComProtocol::PROTOCOL_TRANSFERT_KIND: // inRD->hasAttach() )
			{
				return( popMessage_transfert(ENV, aRoutingRID, aRoutingData) );
			}

			case ComProtocol::PROTOCOL_BUFFER_KIND:
			case ComProtocol::PROTOCOL_BROADCAST_KIND:
			case ComProtocol::PROTOCOL_MULTICAST_KIND:
			case ComProtocol::PROTOCOL_UNICAST_KIND:
			case ComProtocol::PROTOCOL_ANYCAST_KIND:
			{
				return( popMessage_buffer(ENV, aRoutingRID, aRoutingData) );
			}

			case ComProtocol::PROTOCOL_RDV_KIND:
			case ComProtocol::PROTOCOL_MULTIRDV_KIND:
			{
				return( popMessage_rdv(ENV, aRoutingRID, aRoutingData) );
			}

			case ComProtocol::PROTOCOL_UNDEFINED_KIND:
			default:
			{
				AVM_OS_EXIT( FAILED )
						<< "popMessage :> Unknown Protocol for interaction << "
						<< aPort->strComPointNature() << ": "
						<< aPort->getFullyQualifiedNameID() << " >> & << machine: "
						<< aRoutingRID.getInstance()->getFullyQualifiedNameID()
						<< " >> in running context: << "
						<< ENV.mARG->outED->mRID.getInstance()->getFullyQualifiedNameID()
						<< " >> !!!"
						<< SEND_EXIT;

				return( false );
			}
		}
	}
	else
	{
		AVM_OS_EXIT( FAILED )
				<< "popMessage :> Unfound RoutingData for interaction << "
				<< aPort->strComPointNature() << ": "
				<< aPort->getFullyQualifiedNameID() << " >> & << machine: "
				<< aRoutingRID.getInstance()->getFullyQualifiedNameID()
				<< " >> in running context: << "
				<< ENV.mARG->outED->mRID.getInstance()->getFullyQualifiedNameID()
				<< " >> !!!"
				<< SEND_EXIT;
	}

	return( false );
}


bool AvmCommunicationFactory::popMessage_environment(ExecutionEnvironment & ENV,
		const RuntimeID & aRoutingRID, const RoutingData & aRoutingData,
		avm_size_t firstParameterOffset /*= 1*/)
{
	BFCode aTraceInput(OperatorManager::OPERATOR_INPUT_ENV, ENV.mARG->at(0));

	bool allSuccess = true;

	if( ENV.inCODE->populated() )
	{
		ENV.mARG->outED.makeModifiableParamTable();

		InstanceOfPort * aPort = ENV.mARG->at(0).to_ptr< InstanceOfPort >();
		avm_size_t offset = 0;

		InstanceOfData * aVar = NULL;
		BF aNewSymbolicConstant;
		BFList paramList;

		for( ENV.mARG->begin(firstParameterOffset) ; ENV.mARG->hasNext() ;
				ENV.mARG->next() , ++offset )
		{
			paramList.clear();

			aVar = ENV.mARG->current().to_ptr< InstanceOfData >();

			aNewSymbolicConstant = ENV.createNewFreshParam(
					ENV.mARG->outED->mRID,
					aPort->getParameterType(offset),
					aVar, paramList);

			if( not ENV.setRvalue(ENV.mARG->outED, aVar, aNewSymbolicConstant) )
			{
				allSuccess = false;

				break;
			}

			ENV.mARG->outED.appendParameters( paramList );

			aTraceInput->append( aNewSymbolicConstant );
		}
	}

	if( allSuccess )
	{
		ExecutionDataFactory::appendIOElementTrace(ENV.mARG->outED,
				BF( new ExecutionConfiguration(
						ENV.mARG->outED->mRID, aTraceInput) ) );

		ENV.outEDS.append( ENV.mARG->outED );

		return( true );
	}
	else
	{
		return( false );
	}
}


bool AvmCommunicationFactory::popMessage_transfert(ExecutionEnvironment & ENV,
		const RuntimeID & aRoutingRID, const RoutingData & aRoutingData)
{
	return( false );
}


bool AvmCommunicationFactory::popMessage_buffer(ExecutionEnvironment & ENV,
		const RuntimeID & aRoutingRID, const RoutingData & aRoutingData)
{
AVM_IF_DEBUG_FLAG( STATEMENT_COMMUNICATION )
	AVM_OS_TRACE << TAB << "begin "
			"AvmCommunicationFactory::popMessage_buffer" << std::endl;

	ENV.mARG->outED->getRuntime(aRoutingRID).toStreamData(
			ENV.mARG->outED, AVM_OS_TRACE << INCR2_INDENT);
	AVM_OS_TRACE << DECR2_INDENT;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_COMMUNICATION )

	Message popMsg;

	RuntimeID bufferDeclRID = aRoutingRID;

	ListOfInstanceOfBuffer::const_iterator itBuffer =
			aRoutingData.getBufferInstance().begin();
	ListOfInstanceOfBuffer::const_iterator endBuffer =
			aRoutingData.getBufferInstance().end();
	for( ; itBuffer != endBuffer ; ++itBuffer )
	{
		bufferDeclRID = ENV.mARG->outED->getRuntimeContainerRID(
				ENV.mARG->outED->mRID, (*itBuffer) );

		if( bufferDeclRID.valid() )
		{
			if( ENV.mARG->outED->getRuntime(bufferDeclRID).
					getBuffer( *itBuffer ).nonempty() )
			{
				BaseBufferForm & bbf = ENV.mARG->outED.getWritableRuntime(
						bufferDeclRID ).getWritableBuffer( *itBuffer);

				popMsg = bbf.pop(aRoutingData.getMID(), ENV.mARG->outED->mRID);

				if( popMsg.valid() )
				{
					break;
				}
			}
		}
	}

	if( popMsg.valid() )
	{
		BFCode aTraceInput(OperatorManager::OPERATOR_INPUT, ENV.mARG->at(0));

		Message::const_iterator itVal = popMsg.getParameters().begin();
		Message::const_iterator endVal = popMsg.getParameters().end();

		// We have to ignore the << Port >> InstanceOfPort
		for( ENV.mARG->begin(1) ; (itVal != endVal) && ENV.mARG->hasNext() ;
				ENV.mARG->next() , ++itVal )
		{
			if( ENV.setRvalue(ENV.mARG->outED,
					ENV.mARG->current().to_ptr< InstanceOfData >(), *itVal) )
			{
				aTraceInput->append( *itVal );

			}
			else
			{
				return( false );
			}
		}

		ExecutionDataFactory::appendIOElementTrace(ENV.mARG->outED,
				BF( new ExecutionConfiguration(
						ENV.mARG->outED->mRID, aTraceInput, popMsg) ) );

		ENV.outEDS.append( ENV.mARG->outED );

AVM_IF_DEBUG_FLAG( STATEMENT_COMMUNICATION )
	ENV.mARG->outED->getRuntime(aRoutingRID).toStreamData(
			ENV.mARG->outED, AVM_OS_TRACE << INCR2_INDENT);
	AVM_OS_TRACE << DECR2_INDENT_TAB << "end "
			"AvmCommunicationFactory::popMessage_buffer" << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_COMMUNICATION )

		return( true );
	}
	else
	{
		return( false );
	}
}


bool AvmCommunicationFactory::popMessage_rdv(ExecutionEnvironment & ENV,
		const RuntimeID & aRoutingRID, const RoutingData & aRoutingData)
{
	Message inMsg( RuntimeID::REF_NULL,
			ENV.mARG->outED->mRID, aRoutingData.getPort() );
	inMsg.setMID( aRoutingData.getMID() );

	// We have to ignore the << Port >> InstanceOfPort
	for( ENV.mARG->begin(1) ; ENV.mARG->hasNext() ; ENV.mARG->next() )
	{
		inMsg.appendParameter( ENV.mARG->current() );
	}

	ENV.mARG->outED.pushExecSyncPoint( new ExecutionSynchronizationPoint(
			AWAITING_POINT_INPUT_NATURE, aRoutingRID, aRoutingData, inMsg) );

	ENV.appendSync_mwsetAEES(ENV.mARG->outED, AEES_WAITING_INCOM_RDV);

	return( true );
}


/*
 * POP MESSAGE FROM
 */

bool AvmCommunicationFactory::popMessageFrom(ExecutionEnvironment & ENV)
{
	RuntimeID aRoutingRID = ENV.mARG->outED->mRID;
	InstanceOfPort * aPort = ENV.mARG->at(0).to_ptr< InstanceOfPort >();

	const RoutingData & aRoutingData =
			searchInputRoutingData(ENV.mARG->outED, aPort, aRoutingRID);

	RuntimeID aSenderRID = ENV.mARG->at(1).bfRID();

	if( aRoutingData != NULL )
	{
		switch( aRoutingData.getProtocol() )
		{
			case ComProtocol::PROTOCOL_ENVIRONMENT_KIND:
			{
				if( ENV.mARG->outED->getRuntime(aRoutingRID).
						isEnvironmentEnabledCommunication() )
				{
					return( popMessage_environment(ENV,
							aRoutingRID, aRoutingData) );
				}
				return( false );
			}

			case ComProtocol::PROTOCOL_TRANSFERT_KIND: // inRD->hasAttach() )
			{
				return( popMessageFrom_transfert(ENV,
						aSenderRID, aRoutingRID, aRoutingData) );
			}

			case ComProtocol::PROTOCOL_BUFFER_KIND:
			case ComProtocol::PROTOCOL_BROADCAST_KIND:
			case ComProtocol::PROTOCOL_MULTICAST_KIND:
			case ComProtocol::PROTOCOL_UNICAST_KIND:
			case ComProtocol::PROTOCOL_ANYCAST_KIND:
			{
				return( popMessageFrom_buffer(ENV,
						aSenderRID, aRoutingRID, aRoutingData) );
			}

			case ComProtocol::PROTOCOL_RDV_KIND:
			case ComProtocol::PROTOCOL_MULTIRDV_KIND:
			{
				return( popMessageFrom_rdv(ENV,
						aSenderRID, aRoutingRID, aRoutingData) );
			}
			case ComProtocol::PROTOCOL_UNDEFINED_KIND:
			default:
			{
				AVM_OS_EXIT( FAILED )
						<< "popMessageFrom :> Unknown Protocol for interaction << "
						<< aPort->strComPointNature() << ": "
						<< aPort->getFullyQualifiedNameID() << " >> & << machine: "
						<< aRoutingRID.getInstance()->getFullyQualifiedNameID()
						<< " >> in running context: << "
						<< ENV.mARG->outED->mRID.getInstance()->getFullyQualifiedNameID()
						<< " >> !!!"
						<< SEND_EXIT;

				return( false );
			}
		}
	}
	else
	{
		AVM_OS_EXIT( FAILED )
				<< "popMessageFrom :> Unfound RoutingData for interaction << "
				<< aPort->strComPointNature() << ": "
				<< aPort->getFullyQualifiedNameID() << " >> & << machine: "
				<< aRoutingRID.getInstance()->getFullyQualifiedNameID()
				<< " >> in running context: << "
				<< ENV.mARG->outED->mRID.getInstance()->getFullyQualifiedNameID()
				<< " >> !!!"
				<< SEND_EXIT;
	}

	return( false );

}


bool AvmCommunicationFactory::popMessageFrom_transfert(
		ExecutionEnvironment & ENV, const RuntimeID & aSenderRID,
		const RuntimeID & aRoutingRID, const RoutingData & aRoutingData)
{
	return( false );
}


bool AvmCommunicationFactory::popMessageFrom_buffer(
		ExecutionEnvironment & ENV, const RuntimeID & aSenderRID,
		const RuntimeID & aRoutingRID, const RoutingData & aRoutingData)
{
AVM_IF_DEBUG_FLAG( STATEMENT_COMMUNICATION )
	AVM_OS_TRACE << TAB << "begin "
			"AvmCommunicationFactory::popMessageFrom_buffer" << std::endl;

	ENV.mARG->outED->getRuntime(aRoutingRID).toStreamData(
			ENV.mARG->outED, AVM_OS_TRACE << INCR2_INDENT);
	AVM_OS_TRACE << DECR2_INDENT;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_COMMUNICATION )

	Message popMsg;

	RuntimeID bufferDeclRID = aRoutingRID;

	ListOfInstanceOfBuffer::const_iterator itBuffer =
			aRoutingData.getBufferInstance().begin();
	ListOfInstanceOfBuffer::const_iterator endBuffer =
			aRoutingData.getBufferInstance().end();
	for( ; itBuffer != endBuffer ; ++itBuffer )
	{
		bufferDeclRID = ENV.mARG->outED->getRuntimeContainerRID(
				ENV.mARG->outED->mRID, (*itBuffer));

		if( bufferDeclRID.valid() )
		{
			BaseBufferForm & bbf = ENV.mARG->outED.getWritableRuntime(
					bufferDeclRID ).getWritableBuffer( *itBuffer );

			popMsg = bbf.top();
			if( popMsg.valid() && popMsg.isSender(aSenderRID) )
			{
				popMsg = bbf.pop(aRoutingData.getMID(), ENV.mARG->outED->mRID);
			}

			if( popMsg.valid() )
			{
				break;
			}
		}
	}

AVM_IF_DEBUG_FLAG( STATEMENT_COMMUNICATION )
	ENV.mARG->outED->getRuntime(aRoutingRID).toStreamData(
			ENV.mARG->outED, AVM_OS_TRACE << INCR2_INDENT);
	AVM_OS_TRACE << DECR2_INDENT_TAB << "end "
			"AvmCommunicationFactory::popMessageFrom_buffer" << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_COMMUNICATION )

	if( popMsg.valid() )
	{
		BFCode aTraceInput(OperatorManager::OPERATOR_INPUT, ENV.mARG->at(0));

		Message::const_iterator itVal = popMsg.beginParameters();
		Message::const_iterator endVal = popMsg.endParameters();

		// We have to ignore the << Port >> InstanceOfPort and the << Sender >>
		for( ENV.mARG->begin(2) ; (itVal != endVal) && ENV.mARG->hasNext() ;
				ENV.mARG->next() , ++itVal )
		{
			if( ENV.setRvalue(ENV.mARG->outED,
					ENV.mARG->current().to_ptr< InstanceOfData >(), *itVal) )
			{
				aTraceInput->append( *itVal );

			}
			else
			{
				return( false );
			}
		}

		ExecutionDataFactory::appendIOElementTrace(ENV.mARG->outED,
				BF( new ExecutionConfiguration(
						ENV.mARG->outED->mRID, aTraceInput, popMsg) ) );

		ENV.outEDS.append( ENV.mARG->outED );

AVM_IF_DEBUG_FLAG( STATEMENT_COMMUNICATION )
	ENV.mARG->outED->getRuntime(aRoutingRID).toStreamData(
			ENV.mARG->outED, AVM_OS_TRACE << INCR2_INDENT);
	AVM_OS_TRACE << DECR2_INDENT_TAB << "end "
			"AvmCommunicationFactory::popMessageFrom_buffer"
			<< std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_COMMUNICATION )

		return( true );
	}
	else
	{
		return( false );
	}
}


bool AvmCommunicationFactory::popMessageFrom_rdv(
		ExecutionEnvironment & ENV, const RuntimeID & aSenderRID,
		const RuntimeID & aRoutingRID, const RoutingData & aRoutingData)
{
	Message inMsg( aSenderRID, ENV.mARG->outED->mRID, aRoutingData.getPort() );
	inMsg.setMID( aRoutingData.getMID() );

	// We have to ignore the << Port >> InstanceOfPort and the << Sender >>
	for( ENV.mARG->begin(2) ; ENV.mARG->hasNext() ; ENV.mARG->next() )
	{
		inMsg.appendParameter( ENV.mARG->current() );
	}

	ENV.mARG->outED.pushExecSyncPoint( new ExecutionSynchronizationPoint(
			AWAITING_POINT_INPUT_NATURE, aRoutingRID, aRoutingData, inMsg) );

	ENV.appendSync_mwsetAEES(ENV.mARG->outED, AEES_WAITING_INCOM_RDV);

	return( true );
}


/*
 * PUSH MESSAGE
 */
bool AvmCommunicationFactory::pushMessage(ExecutionEnvironment & ENV,
		const Message & anOutputMsg, RuntimeID aRoutingRID)
{
	InstanceOfPort * aPort = anOutputMsg.getPort();

	const RoutingData & aRoutingData =
			searchOutputRoutingData(ENV.mARG->outED, aPort, aRoutingRID);

	if( aRoutingData != NULL )
	{
		anOutputMsg.setMID( aRoutingData.getMID() );

		switch( aRoutingData.getProtocol() )
		{
			case ComProtocol::PROTOCOL_ENVIRONMENT_KIND:
			{
				return( pushMessage_environment(ENV,
						aRoutingRID, aRoutingData, anOutputMsg) );
			}

			case ComProtocol::PROTOCOL_TRANSFERT_KIND: // aRoutingData.hasAttach()
			{
				return( pushMessage_transfert(ENV,
						aRoutingRID, aRoutingData, anOutputMsg) );
			}

			case ComProtocol::PROTOCOL_BUFFER_KIND:
			{
				return( pushMessage_buffer(ENV,
						aRoutingRID, aRoutingData, anOutputMsg) );
			}

			case ComProtocol::PROTOCOL_RDV_KIND:
			case ComProtocol::PROTOCOL_MULTIRDV_KIND:
			{
				return( pushMessage_rdv(ENV,
						aRoutingRID, aRoutingData, anOutputMsg) );
			}

			case ComProtocol::PROTOCOL_BROADCAST_KIND:
			{
				return( pushMessage_broadcast(ENV,
						aRoutingRID, aRoutingData, anOutputMsg) );
			}

			case ComProtocol::PROTOCOL_MULTICAST_KIND:
			{
				return( pushMessage_multicast(ENV,
						aRoutingRID, aRoutingData, anOutputMsg) );
			}
			case ComProtocol::PROTOCOL_UNICAST_KIND:
			{
				return( pushMessage_unicast(ENV,
						aRoutingRID, aRoutingData, anOutputMsg) );
			}

			case ComProtocol::PROTOCOL_ANYCAST_KIND:
			{
				return( pushMessage_anycast(ENV,
						aRoutingRID, aRoutingData, anOutputMsg) );
			}

			case ComProtocol::PROTOCOL_UNDEFINED_KIND:
			default:
			{
//				return( pushMessage_environment(anED, ENV.mARG->outED->mRID,
//						aRoutingRF, aRoutingData, anOutputMsg, listOfOutputED) );
				return( false );
			}
		}
	}
	else
	{
		AVM_OS_EXIT( FAILED )
			<< "Push message error : Unfound RoutingData for interaction << "
			<<  aPort->strComPointNature() << ": "
			<< aRoutingRID.getInstance()->getFullyQualifiedNameID()
			<< " >> in running context: << "
			<< aPort->getFullyQualifiedNameID() << " >> & << machine: "
			<< ENV.mARG->outED->mRID.getInstance()->getFullyQualifiedNameID()
			<< " >> !!!"
			<< SEND_EXIT;
	}

	return( false );
}


bool AvmCommunicationFactory::pushMessage_environment(
		ExecutionEnvironment & ENV, const RuntimeID & aRoutingRID,
		const RoutingData & aRoutingData, const Message & anOutputMsg)
{
	BFCode aTraceOutput(OperatorManager::OPERATOR_OUTPUT_ENV,
			anOutputMsg.bfPort());

	aTraceOutput->append( anOutputMsg.getParameters() );

	ExecutionDataFactory::appendIOElementTrace(ENV.mARG->outED,
			BF( new ExecutionConfiguration(
					ENV.mARG->outED->mRID, aTraceOutput, anOutputMsg) ) );

	ENV.outEDS.append( ENV.mARG->outED );

	return( true );
}


bool AvmCommunicationFactory::pushMessage_transfert(
		ExecutionEnvironment & ENV, const RuntimeID & aRoutingRID,
		const RoutingData & aRoutingData, const Message & anOutputMsg)
{
	return( true );
}

bool AvmCommunicationFactory::pushMessage_buffer(
		ExecutionEnvironment & ENV, const RuntimeID & aRoutingRID,
		const RoutingData & aRoutingData, const Message & anOutputMsg)
{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , STATEMENT_COMMUNICATION )
	AVM_OS_TRACE << TAB << "begin "
			"AvmCommunicationFactory::pushMessage_buffer" << std::endl;

	ENV.mARG->outED->getRuntime(aRoutingRID).toStream(
			AVM_OS_TRACE << INCR2_INDENT );
	AVM_OS_TRACE << DECR2_INDENT;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , STATEMENT_COMMUNICATION )

	bool oneSuccess = false;

	RuntimeID bufferDeclRID = aRoutingRID;

	ListOfInstanceOfBuffer::const_iterator itBuffer =
			aRoutingData.getBufferInstance().begin();
	ListOfInstanceOfBuffer::const_iterator endBuffer =
			aRoutingData.getBufferInstance().end();
	for( ; itBuffer != endBuffer ; ++itBuffer )
	{
		bufferDeclRID = ENV.mARG->outED->getRuntimeContainerRID(
				aRoutingRID, (*itBuffer));

		if( bufferDeclRID.valid() )
		{
			APExecutionData outED = ENV.mARG->outED;

			BaseBufferForm & bbf = outED.getWritableRuntime(
					bufferDeclRID ).getWritableBuffer( *itBuffer );

			if( bbf.push( anOutputMsg ) )
			{
				oneSuccess = true;

				BFCode aTraceOutput(OperatorManager::OPERATOR_OUTPUT,
						anOutputMsg.bfPort());

				aTraceOutput->append( anOutputMsg.getParameters() );

				ExecutionDataFactory::appendIOElementTrace(outED,
						BF( new ExecutionConfiguration(
								outED->mRID, aTraceOutput, anOutputMsg) ) );

				ENV.outEDS.append( outED );


AVM_IF_DEBUG_LEVEL_FLAG( HIGH , STATEMENT_COMMUNICATION )
	outED->getRuntime(aRoutingRID).toStream( AVM_OS_TRACE << INCR2_INDENT );
	AVM_OS_TRACE << DECR2_INDENT_TAB
			<< "end AvmCommunicationFactory::pushMessage_buffer" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , STATEMENT_COMMUNICATION )
			}
		}
	}

	return( oneSuccess );
}


bool AvmCommunicationFactory::pushMessage_rdv(
		ExecutionEnvironment & ENV, const RuntimeID & aRoutingRID,
		const RoutingData & aRoutingData, const Message & anOutputMsg)
{
	ENV.mARG->outED.pushExecSyncPoint(new ExecutionSynchronizationPoint(
		AWAITING_POINT_OUTPUT_NATURE, aRoutingRID, aRoutingData, anOutputMsg) );

	ENV.appendSync_mwsetAEES(ENV.mARG->outED, AEES_WAITING_OUTCOM_RDV);

	return( true );
}


bool AvmCommunicationFactory::pushMessage_broadcast(
		ExecutionEnvironment & ENV, const RuntimeID & aRoutingRID,
		const RoutingData & aRoutingData, const Message & anOutputMsg)
{
	return( true );
}


bool AvmCommunicationFactory::pushMessage_multicast(
		ExecutionEnvironment & ENV, const RuntimeID & aRoutingRID,
		const RoutingData & aRoutingData, const Message & anOutputMsg)
{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , STATEMENT_COMMUNICATION )
	AVM_OS_TRACE << TAB << "begin "
			"AvmCommunicationFactory::pushMessage_multicast" << std::endl;

	ENV.mARG->outED->getRuntime(aRoutingRID).toStream(
			AVM_OS_TRACE << INCR2_INDENT );
	AVM_OS_TRACE << DECR2_INDENT;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , STATEMENT_COMMUNICATION )

	bool oneSuccess = false;

	RuntimeID bufferDeclRID = aRoutingRID;

	ListOfInstanceOfBuffer::const_iterator itBuffer =
			aRoutingData.getBufferInstance().begin();
	ListOfInstanceOfBuffer::const_iterator endBuffer =
			aRoutingData.getBufferInstance().end();
	for( ; itBuffer != endBuffer ; ++itBuffer )
	{
		bufferDeclRID = ENV.mARG->outED->getRuntimeContainerRID(
				aRoutingRID, (*itBuffer));

		if( bufferDeclRID.valid() )
		{
			BaseBufferForm & bbf = ENV.mARG->outED.getWritableRuntime(
					bufferDeclRID ).getWritableBuffer( *itBuffer );

			if( bbf.push( anOutputMsg ) )
			{
				oneSuccess = true;
			}
		}
	}

	if( oneSuccess )
	{
		BFCode aTraceOutput(OperatorManager::OPERATOR_OUTPUT,
				anOutputMsg.bfPort());

		aTraceOutput->append( anOutputMsg.getParameters() );

		ExecutionDataFactory::appendIOElementTrace(ENV.mARG->outED,
				BF( new ExecutionConfiguration(
						ENV.mARG->outED->mRID, aTraceOutput, anOutputMsg) ) );

		ENV.outEDS.append( ENV.mARG->outED );


AVM_IF_DEBUG_LEVEL_FLAG( HIGH , STATEMENT_COMMUNICATION )
	ENV.mARG->outED->getRuntime(aRoutingRID).toStream(
			AVM_OS_TRACE << INCR2_INDENT );
	AVM_OS_TRACE << DECR2_INDENT_TAB
			<< "end AvmCommunicationFactory::pushMessage_buffer"
			<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , STATEMENT_COMMUNICATION )

		return( true );
	}
	else
	{
		return( false );
	}
}


bool AvmCommunicationFactory::pushMessage_unicast(
		ExecutionEnvironment & ENV, const RuntimeID & aRoutingRID,
		const RoutingData & aRoutingData, const Message & anOutputMsg)
{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , STATEMENT_COMMUNICATION )
	AVM_OS_TRACE << TAB << "begin "
			"AvmCommunicationFactory::pushMessage_multicast" << std::endl;

	ENV.mARG->outED->getRuntime(aRoutingRID).toStream(
			AVM_OS_TRACE << INCR2_INDENT );
	AVM_OS_TRACE << DECR2_INDENT;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , STATEMENT_COMMUNICATION )

	bool oneSuccess = false;

	RuntimeID bufferDeclRID = aRoutingRID;

	ListOfInstanceOfBuffer::const_iterator itBuffer =
			aRoutingData.getBufferInstance().begin();
	ListOfInstanceOfBuffer::const_iterator endBuffer =
			aRoutingData.getBufferInstance().end();
	for( ; itBuffer != endBuffer ; ++itBuffer )
	{
		bufferDeclRID = ENV.mARG->outED->getRuntimeContainerRID(
				aRoutingRID, (*itBuffer));

		if( bufferDeclRID.valid() )
		{
			BaseBufferForm & bbf = ENV.mARG->outED.getWritableRuntime(
					bufferDeclRID ).getWritableBuffer( *itBuffer );

			if( bbf.push( anOutputMsg ) )
			{
				oneSuccess = true;

				BFCode aTraceOutput(OperatorManager::OPERATOR_OUTPUT,
						anOutputMsg.bfPort());

				aTraceOutput->append( anOutputMsg.getParameters() );

				ExecutionDataFactory::appendIOElementTrace(ENV.mARG->outED,
					BF( new ExecutionConfiguration(
						ENV.mARG->outED->mRID, aTraceOutput, anOutputMsg) ) );

				ENV.outEDS.append( ENV.mARG->outED );

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , STATEMENT_COMMUNICATION )
	ENV.mARG->outED->getRuntime(aRoutingRID).toStream(
			AVM_OS_TRACE << INCR2_INDENT );
	AVM_OS_TRACE << DECR2_INDENT_TAB
			<< "end AvmCommunicationFactory::pushMessage_buffer"
			<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , STATEMENT_COMMUNICATION )
			}
		}
	}

	return( oneSuccess );
}


bool AvmCommunicationFactory::pushMessage_anycast(
		ExecutionEnvironment & ENV, const RuntimeID & aRoutingRID,
		const RoutingData & aRoutingData, const Message & anOutputMsg)
{
	return( pushMessage_buffer(ENV, aRoutingRID, aRoutingData, anOutputMsg) );
//	return( true );
}



/*
 * PUSH MESSAGE TO
 */

bool AvmCommunicationFactory::pushMessageTo(
		ExecutionEnvironment & ENV, const Message & anOutputMsg)
{
	RuntimeID aRoutingRID = ENV.mARG->outED->mRID;
	InstanceOfPort * aPort = anOutputMsg.getPort();

	const RoutingData & aRoutingData =
			searchOutputRoutingData(ENV.mARG->outED, aPort, aRoutingRID);

	if( aRoutingData != NULL )
	{
		anOutputMsg.setMID( aRoutingData.getMID() );

		if( (anOutputMsg.getReceiverRID() == RuntimeLib::RID_ENVIRONMENT) ||
				(anOutputMsg.getReceiverRID() == RuntimeLib::RID_NIL) )
		{
			return( pushMessage_environment(ENV,
					aRoutingRID, aRoutingData, anOutputMsg) );
		}

		switch( aRoutingData.getProtocol() )
		{
			case ComProtocol::PROTOCOL_ENVIRONMENT_KIND:
			{
				return( pushMessage_environment(ENV,
						aRoutingRID, aRoutingData, anOutputMsg) );
			}

			case ComProtocol::PROTOCOL_TRANSFERT_KIND:
			{// aRoutingData.hasAttach() )
				return( pushMessageTo_transfert(ENV,
						aRoutingRID, aRoutingData, anOutputMsg) );
			}

			case ComProtocol::PROTOCOL_BUFFER_KIND:
			{
				return( pushMessageTo_buffer(ENV,
						aRoutingRID, aRoutingData, anOutputMsg) );
			}

			case ComProtocol::PROTOCOL_RDV_KIND:
			case ComProtocol::PROTOCOL_MULTIRDV_KIND:
			{
				return( pushMessageTo_rdv(ENV,
						aRoutingRID, aRoutingData, anOutputMsg) );
			}

			case ComProtocol::PROTOCOL_BROADCAST_KIND:
			{
				return( pushMessageTo_broadcast(ENV,
						aRoutingRID, aRoutingData, anOutputMsg) );
			}

			case ComProtocol::PROTOCOL_MULTICAST_KIND:
			{
				return( pushMessageTo_multicast(ENV,
						aRoutingRID, aRoutingData, anOutputMsg) );
			}
			case ComProtocol::PROTOCOL_UNICAST_KIND:
			{
				return( pushMessageTo_unicast(ENV,
						aRoutingRID, aRoutingData, anOutputMsg) );
			}

			case ComProtocol::PROTOCOL_ANYCAST_KIND:
			{
				return( pushMessageTo_anycast(ENV,
						aRoutingRID, aRoutingData, anOutputMsg) );
			}

			case ComProtocol::PROTOCOL_UNDEFINED_KIND:
			default:
			{
				AVM_OS_EXIT( FAILED )
						<< "pushMessageTo :> Unknown Protocol for interaction << "
						<< aPort->strComPointNature() << ": "
						<< aPort->getFullyQualifiedNameID() << " >> & << machine: "
						<< ENV.mARG->outED->mRID.getInstance()->getFullyQualifiedNameID()
						<< " >> !!!"
						<< SEND_EXIT;

				return( false );
			}
		}
	}
	else
	{
		AVM_OS_EXIT( FAILED )
				<< "pushMessageTo :> Unfound RoutingData for interaction << "
				<< aPort->strComPointNature() << ": "
				<< aPort->getFullyQualifiedNameID() << " >> & << machine: "
				<< aRoutingRID.getInstance()->getFullyQualifiedNameID()
				<< " >> in running context: << "
				<< ENV.mARG->outED->mRID.getInstance()->getFullyQualifiedNameID()
				<< " >> !!!"
				<< SEND_EXIT;
	}

	return( false );
}


bool AvmCommunicationFactory::pushMessageTo_transfert(
		ExecutionEnvironment & ENV, const RuntimeID & aRoutingRID,
		const RoutingData & aRoutingData, const Message & anOutputMsg)
{
	return( true );
}


bool AvmCommunicationFactory::pushMessageTo_buffer(
		ExecutionEnvironment & ENV, const RuntimeID & aRoutingRID,
		const RoutingData & aRoutingData, const Message & anOutputMsg)
{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , STATEMENT_COMMUNICATION )
	AVM_OS_TRACE << TAB << "begin "
			"AvmCommunicationFactory::pushMessageTo_buffer" << std::endl;

	ENV.mARG->outED->getRuntime(aRoutingRID).toStream(
			AVM_OS_TRACE << INCR2_INDENT );
	AVM_OS_TRACE << DECR2_INDENT;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , STATEMENT_COMMUNICATION )

	// Search receiver machine in the INPUT MACHINE-PORT connected list
	bool oneSuccess = false;

	ListOfInstanceOfBuffer::const_iterator itbIn;
	ListOfInstanceOfBuffer::const_iterator itbInEnd;

	ListOfInstanceOfBuffer::const_iterator itbOut;
	ListOfInstanceOfBuffer::const_iterator itbOutEnd;

	const VectorOfPairMachinePort & theConnectedPort =
			aRoutingRID.getExecutable()->getConnect().at(
					aRoutingData.getConnect()->getOffset() ).
							getInputComRouteData().getMachinePorts();

	RuntimeID bufferDeclRID = aRoutingRID;

	VectorOfPairMachinePort::const_iterator itMP = theConnectedPort.begin();
	VectorOfPairMachinePort::const_iterator endMP = theConnectedPort.end();
	for( ; itMP != endMP ; ++itMP )
	{
		if( anOutputMsg.isReceiverMachine( (*itMP)->first() ) )
		{
			// get Routing Data of the connector input receiver candidate
			const RoutingData & connectInputRD =
					ENV.mARG->outED->getRuntime(
						anOutputMsg.getReceiverRID() ).getRouter().
						getInputRouting( (*itMP)->second()->getRouteOffset() );

			// Push the message in all COMMON buffer with the OUTPUT PORT!
			itbIn = connectInputRD.getBufferInstance().begin();
			itbInEnd = connectInputRD.getBufferInstance().end();
			for(  ; itbIn != itbInEnd ; ++itbIn )
			{
				itbOut = aRoutingData.getBufferInstance().begin();
				itbOutEnd = aRoutingData.getBufferInstance().end();
				for(  ; itbOut != itbOutEnd ; ++itbOut )
				{
					if( (*itbIn) == (*itbOut) )  // COMMON BUFFER found
					{
						bufferDeclRID = ENV.mARG->outED->getRuntimeContainerRID(
								anOutputMsg.getReceiverRID(), (*itbOut) );

						BaseBufferForm & bbf =
							ENV.mARG->outED.getWritableRuntime(
								bufferDeclRID ).getWritableBuffer( *itbOut );

						if( bbf.push( anOutputMsg ) )
						{
							oneSuccess = true;
						}
					}
				}
			}
		}
	}

	if( oneSuccess )
	{
		BFCode aTraceOutput(OperatorManager::OPERATOR_OUTPUT,
				anOutputMsg.bfPort());

		aTraceOutput->append( anOutputMsg.getParameters() );

		ExecutionDataFactory::appendIOElementTrace(ENV.mARG->outED,
				BF( new ExecutionConfiguration(
						ENV.mARG->outED->mRID, aTraceOutput, anOutputMsg) ) );

		ENV.outEDS.append( ENV.mARG->outED );


AVM_IF_DEBUG_LEVEL_FLAG( HIGH , STATEMENT_COMMUNICATION )
	ENV.mARG->outED->getRuntime(aRoutingRID).toStream(
			AVM_OS_TRACE << INCR2_INDENT );
	AVM_OS_TRACE << DECR2_INDENT_TAB
			<< "end AvmCommunicationFactory::pushMessageTo_buffer"
			<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , STATEMENT_COMMUNICATION )

		return( true );
	}
	else
	{
		return( false );
	}
}


bool AvmCommunicationFactory::pushMessageTo_rdv(
		ExecutionEnvironment & ENV, const RuntimeID & aRoutingRID,
		const RoutingData & aRoutingData, const Message & anOutputMsg)
{
	ENV.mARG->outED.pushExecSyncPoint( new ExecutionSynchronizationPoint(
			AWAITING_POINT_OUTPUT_NATURE,
			aRoutingRID, aRoutingData, anOutputMsg) );

	ENV.appendSync_mwsetAEES(ENV.mARG->outED, AEES_WAITING_OUTCOM_RDV);

	return( true );
}


bool AvmCommunicationFactory::pushMessageTo_broadcast(
		ExecutionEnvironment & ENV, const RuntimeID & aRoutingRID,
		const RoutingData & aRoutingData, const Message & anOutputMsg)
{
	return( true );
}


bool AvmCommunicationFactory::pushMessageTo_multicast(
		ExecutionEnvironment & ENV, const RuntimeID & aRoutingRID,
		const RoutingData & aRoutingData, const Message & anOutputMsg)
{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , STATEMENT_COMMUNICATION )
	AVM_OS_TRACE << TAB << "begin "
			"AvmCommunicationFactory::pushMessageTo_buffer" << std::endl;

	ENV.mARG->outED->getRuntime(aRoutingRID).toStream(
			AVM_OS_TRACE << INCR2_INDENT );
	AVM_OS_TRACE << DECR2_INDENT;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , STATEMENT_COMMUNICATION )

	// Search receiver machine in the INPUT MACHINE-PORT connected list
	bool oneSuccess = false;

	ListOfInstanceOfBuffer::const_iterator itbIn;
	ListOfInstanceOfBuffer::const_iterator itbInEnd;

	ListOfInstanceOfBuffer::const_iterator itbOut;
	ListOfInstanceOfBuffer::const_iterator itbOutEnd;

	const VectorOfPairMachinePort & theConnectedPort =
			aRoutingRID.getExecutable()->getConnect().at(
					aRoutingData.getConnect()->getOffset() ).
							getInputComRouteData().getMachinePorts();

	RuntimeID bufferDeclRID = aRoutingRID;

	VectorOfPairMachinePort::const_iterator itMP = theConnectedPort.begin();
	VectorOfPairMachinePort::const_iterator endMP = theConnectedPort.end();
	for( ; itMP != endMP ; ++itMP )
	{
		if( anOutputMsg.isReceiverMachine( (*itMP)->first() ) )
		{
			// get Routing Data of the connector input receiver candidate
			const RoutingData & connectInputRD =
					ENV.mARG->outED->getRuntime(
						anOutputMsg.getReceiverRID() ).getRouter().
						getInputRouting( (*itMP)->second()->getRouteOffset() );

			// Push the message in all COMMON buffer with the OUTPUT PORT!
			itbIn = connectInputRD.getBufferInstance().begin();
			itbInEnd = connectInputRD.getBufferInstance().end();
			for(  ; itbIn != itbInEnd ; ++itbIn )
			{
				itbOut = aRoutingData.getBufferInstance().begin();
				itbOutEnd = aRoutingData.getBufferInstance().end();
				for(  ; itbOut != itbOutEnd ; ++itbOut )
				{
					if( (*itbIn) == (*itbOut) )  // COMMON BUFFER found
					{
						bufferDeclRID = ENV.mARG->outED->getRuntimeContainerRID(
								anOutputMsg.getReceiverRID(), (*itbOut) );

						BaseBufferForm & bbf =
							ENV.mARG->outED.getWritableRuntime(
								bufferDeclRID ).getWritableBuffer( *itbOut );

						if( bbf.push( anOutputMsg ) )
						{
							oneSuccess = true;
						}
					}
				}
			}
		}
	}

	if( oneSuccess )
	{
		BFCode aTraceOutput(OperatorManager::OPERATOR_OUTPUT,
				anOutputMsg.bfPort());

		aTraceOutput->append( anOutputMsg.getParameters() );

		ExecutionDataFactory::appendIOElementTrace(ENV.mARG->outED,
				BF(new ExecutionConfiguration(
						ENV.mARG->outED->mRID, aTraceOutput, anOutputMsg) ) );

		ENV.outEDS.append( ENV.mARG->outED );


AVM_IF_DEBUG_LEVEL_FLAG( HIGH , STATEMENT_COMMUNICATION )
	ENV.mARG->outED->getRuntime(aRoutingRID).toStream(
			AVM_OS_TRACE << INCR2_INDENT );
	AVM_OS_TRACE << DECR2_INDENT_TAB
			<< "end AvmCommunicationFactory::pushMessageTo_buffer"
			<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , STATEMENT_COMMUNICATION )

		return( true );
	}
	else
	{
		return( false );
	}
}


bool AvmCommunicationFactory::pushMessageTo_unicast(
		ExecutionEnvironment & ENV, const RuntimeID & aRoutingRID,
		const RoutingData & aRoutingData, const Message & anOutputMsg)
{
	return( true );
}


bool AvmCommunicationFactory::pushMessageTo_anycast(
		ExecutionEnvironment & ENV, const RuntimeID & aRoutingRID,
		const RoutingData & aRoutingData, const Message & anOutputMsg)
{
	return( pushMessageTo_buffer(ENV, aRoutingRID, aRoutingData, anOutputMsg) );
//	return( true );
}


/*
 * UPDATE BUFFER
 */
bool AvmCommunicationFactory::updateBuffer(APExecutionData & anED)
{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , STATEMENT_COMMUNICATION )
	anED->getRuntime(1).toStream(AVM_OS_TRACE);
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , STATEMENT_COMMUNICATION )

	TableOfBufferT & wrBufferTable = anED.getWritableRuntime(
			anED->mRID ).getWritableBufferTable();

	TableOfBufferT::const_iterator it = wrBufferTable.begin();
	TableOfBufferT::const_iterator itEnd = wrBufferTable.end();
	for( ; it != itEnd ; ++it )
	{
		switch( (*it)->classKind() )
		{
			case FORM_BUFFER_BROADCAST_KIND:
			{
				BroadcastBuffer * theBuffer = (*it)->to< BroadcastBuffer >();
				theBuffer->push( Message::_NULL_ );
				theBuffer->update();

				break;
			}

			default:
			{
				break;
			}
		}
	}

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , STATEMENT_COMMUNICATION )
	anED->getRuntime(1).toStream(AVM_OS_TRACE);
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , STATEMENT_COMMUNICATION )

	return( true );
}


/*
 * PRESENCE / ABSENCE status
 */
bool AvmCommunicationFactory::computePresence(const ExecutionData & anED,
		const RuntimeID & aReceiverRID, InstanceOfPort * aPort)
{
	RuntimeID aRoutingRID = aReceiverRID;

	const RoutingData & aRoutingData =
			searchInputRoutingData(anED, aPort, aRoutingRID);

	if( aRoutingData != NULL )
	{
		switch( aRoutingData.getProtocol() )
		{
			case ComProtocol::PROTOCOL_ENVIRONMENT_KIND:
			{
				return( true );
			}

			case ComProtocol::PROTOCOL_TRANSFERT_KIND: // inRD->hasAttach() )
			{
				return( false );
			}

			case ComProtocol::PROTOCOL_BUFFER_KIND:
			case ComProtocol::PROTOCOL_BROADCAST_KIND:
			case ComProtocol::PROTOCOL_MULTICAST_KIND:
			case ComProtocol::PROTOCOL_UNICAST_KIND:
			case ComProtocol::PROTOCOL_ANYCAST_KIND:
			{
				RuntimeID bufferDeclRID = aRoutingRID;

				ListOfInstanceOfBuffer::const_iterator itBuffer =
						aRoutingData.getBufferInstance().begin();
				ListOfInstanceOfBuffer::const_iterator endBuffer =
						aRoutingData.getBufferInstance().end();
				for( ; itBuffer != endBuffer ; ++itBuffer )
				{
					bufferDeclRID = anED.getRuntimeContainerRID(
							aReceiverRID, (*itBuffer) );

					if( bufferDeclRID.valid() )
					{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , STATEMENT_COMMUNICATION )
	AVM_OS_TRACE << "computePresence :> "
			<< str_header( aPort ) << std::endl
			<< "RoutingRID  : " << aRoutingRID.getFullyQualifiedNameID()
			<< std::endl
			<< "BufferRID   : " << bufferDeclRID.getFullyQualifiedNameID()
			<< std::endl
			<< "ReceiverRID : " << aReceiverRID.getFullyQualifiedNameID()
			<< std::endl;
	aRoutingData.toStream(AVM_OS_TRACE);
	anED.getRuntime(bufferDeclRID).toStream(AVM_OS_TRACE);
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , STATEMENT_COMMUNICATION )

						const BaseBufferForm & bbf = anED.getRuntime(
								bufferDeclRID ).getBuffer(*itBuffer);

						if( bbf.nonempty() )
						{
							if( aRoutingRID.getExecutable()->
									getSpecifier().hasFeatureInputEnabled() )
							{
								if( bbf.contains(
										aRoutingData.getMID(), aReceiverRID) )
								{
									return( true );
								}
							}
							else if( bbf.isTop(aRoutingData.getMID(),
									aReceiverRID) )
							{
								return( true );
							}
						}
					}
				}

				return( false );
			}

			case ComProtocol::PROTOCOL_RDV_KIND:
			case ComProtocol::PROTOCOL_MULTIRDV_KIND:

			case ComProtocol::PROTOCOL_UNDEFINED_KIND:
			default:
			{
				return( false );
			}
		}
	}

	return( false );
}


/*
 * Collect buffer message
 */
void AvmCommunicationFactory::collectBufferMessage(
		const ExecutionData & anED, BaseBufferForm & aBuffer)
{
	TableOfBufferT::const_iterator itBuffer;
	TableOfBufferT::const_iterator endBuffer;

	TableOfRuntimeT::const_iterator itRF = anED.getTableOfRuntime().begin();
	TableOfRuntimeT::const_iterator endRF = anED.getTableOfRuntime().end();
	for( ; itRF != endRF ; ++itRF )
	{
		if( (*itRF)->hasBufferTable() )
		{
			itBuffer = (*itRF)->getBufferTable().begin();
			endBuffer = (*itRF)->getBufferTable().end();
			for( ; itBuffer != endBuffer ; ++itBuffer )
			{
				(*itBuffer)->copyTo( aBuffer );
			}
		}
	}
}


}
