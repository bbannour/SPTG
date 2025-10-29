/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 26 févr. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmInputEnabledPrimitive.h"

#include <builder/analysis/CommunicationDependency.h>

#include <computer/ExecutionEnvironment.h>
#include <computer/primitive/AvmCommunicationFactory.h>

#include <fml/executable/InstanceOfPort.h>
#include <fml/executable/RoutingData.h>


namespace sep
{

/**
 ***************************************************************************
 * execution of a INPUT_ENABLED program
 ***************************************************************************
 */
bool AvmPrimitive_InputEnabled::run(ExecutionEnvironment & ENV)
{
	ExecutionData outED = ENV.inED;

	const ListOfInstanceOfPort * ieComs  = nullptr;
	const ListOfInstanceOfPort * ieSaves = nullptr;

	ListOfInstanceOfPort ieMutableComs;
	ListOfInstanceOfPort ieMutableSaves;

	// case of a composite machine
	if( outED.getRID().refExecutable().isMutableCommunication() )
	{
		CommunicationDependency::computeInputEnabledCom(outED, outED.getRID(),
				ieMutableComs, ENV.inCODE->first().to< AvmCode >() );

		if( ieMutableComs.empty() )
		{
			return( ENV.run(ENV.inCODE->first().bfCode()) );
		}

		CommunicationDependency::computeInputEnabledSave(outED, outED.getRID(),
				ieMutableSaves, ENV.inCODE->first().to< AvmCode >() );

		ieComs  = & ieMutableComs;
		ieSaves = & ieMutableSaves;

//!!! DEBUG TRACE
AVM_IF_DEBUG_FLAG( STATEMENT_SCHEDULING )
	AVM_OS_TRACE << std::endl << "InputEnabled:mutable> " << outED.getRID().str()
			<< std::endl;
	outED.getRID().refExecutable().getOnRun()->toStream(AVM_OS_TRACE);

	outED.getRID().refExecutable().toStreamStaticCom(AVM_OS_TRACE);

	AVM_OS_TRACE << "com#input_enabled{" << std::endl;
	InstanceOfPort::toStream(AVM_OS_TRACE, ieMutableComs);
	AVM_OS_TRACE << "}" << std::endl;

	if( ieMutableSaves.nonempty() )
	{
		AVM_OS_TRACE << "com#input_enabled#save{" << std::endl;
		InstanceOfPort::toStream(AVM_OS_TRACE, ieMutableSaves);
		AVM_OS_TRACE << "}" << std::endl;
	}
AVM_ENDIF_DEBUG_FLAG( STATEMENT_SCHEDULING )
//!!! END DEBUG TRACE
	}
	else
	{
		// the expected (input) communication element
		ieComs = &(	outED.getRID().refExecutable().getInputEnabledCom() );

		// the save (input) communication element
		ieSaves = &( outED.getRID().refExecutable().getInputEnabledSave() );

//!!! DEBUG TRACE
AVM_IF_DEBUG_FLAG( STATEMENT_SCHEDULING )
	AVM_OS_TRACE << std::endl << "InputEnabled:final> " << outED.getRID().str()
			<< std::endl;
	outED.getRID().refExecutable().getOnRun()->toStream(AVM_OS_TRACE);
	outED.getRID().refExecutable().toStreamStaticCom(AVM_OS_TRACE);
AVM_ENDIF_DEBUG_FLAG( STATEMENT_SCHEDULING )
//!!! END DEBUG TRACE
	}

	ListOfMessage saveMessages;

	// the Buffer Instance
	const InstanceOfBuffer * ieBuffer =
			outED.getRID().refExecutable().getInputEnabledBuffer().front();

	// the runtime buffer machine RID
	RuntimeID tmpRID = outED.getRuntimeContainerRID(ieBuffer);

	// the runtime (reading) buffer
	const BaseBufferForm & readableBuffer =
			outED.getRuntime(tmpRID).getBuffer( ieBuffer );

//!!! DEBUG TRACE
AVM_IF_DEBUG_FLAG( STATEMENT_SCHEDULING )
	AVM_OS_TRACE << ieBuffer->getNameID() << ":>" << std::endl;
	readableBuffer.toFscn(AVM_OS_TRACE, tmpRID);
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_SCHEDULING )
//!!! END DEBUG TRACE

	if( readableBuffer.nonempty() )
	{
		// the runtime non-empty (writing) buffer
		BaseBufferForm & writableBuffer = outED.getWritableRuntime(
				tmpRID ).getWritableBuffer( ieBuffer );

//!!! DEBUG TRACE
AVM_IF_DEBUG_FLAG( STATEMENT_SCHEDULING )
	AVM_OS_TRACE << std::endl << "InputEnabled:av> " << outED.getRID().str()
			<< std::endl;
	outED.getRID().refExecutable().getOnRun()->toStream(AVM_OS_TRACE);

	AVM_OS_TRACE << "com#input_enabled<mutable>{" << std::endl;
	InstanceOfPort::toStream(AVM_OS_TRACE, *ieComs);
	AVM_OS_TRACE << "}" << std::endl;

	if( ieSaves->nonempty() )
	{
		AVM_OS_TRACE << "com#input_enabled#save<mutable>{" << std::endl;
		InstanceOfPort::toStream(AVM_OS_TRACE, *ieSaves);
		AVM_OS_TRACE << "}" << std::endl;
	}

	AVM_OS_TRACE << ieBuffer->getNameID() << ":>" << std::endl;
	writableBuffer.toFscn(AVM_OS_TRACE, tmpRID);
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_SCHEDULING )
//!!! END DEBUG TRACE

		ListOfSizeT ieMidComs;

		for( const auto & itPort : (* ieComs) )
		{
			RuntimeID aRoutingRID = outED.getRID();

			const RoutingData & aRoutingData = ( itPort->hasInputRoutingData()
					? itPort->getInputRoutingData()
					: AvmCommunicationFactory::searchInputRoutingData(
							outED, (* itPort), aRoutingRID ) );

			if( aRoutingData.valid() )
			{
				ieMidComs.append( aRoutingData.getMID() );

				if( aRoutingData.hasManyCastRoutingData() )
				{
					for( const auto & itRoutingData :
							aRoutingData.getManyCastRoutingData() )
					{
						ieMidComs.append( itRoutingData.getMID() );
					}
				}
			}
		}

		if( ieSaves->empty() )
		{
			if( ieMidComs.nonempty() )
			{
				writableBuffer.popBefore( ieMidComs , outED.getRID());
			}
			else if( (*ieComs).nonempty() )
			{
				writableBuffer.popBefore( *ieComs , outED.getRID());
			}
			else
			{
				writableBuffer.popBefore( outED.getRID());
			}
		}
		else
		{
			ListOfSizeT ieMidSaves;
			for( const auto & itPort : (* ieSaves) )
			{
				if( itPort->hasInputRoutingData() )
				{
					ieMidSaves.append( itPort->getInputRoutingData().getMID() );

					const RoutingData & aRoutingData =
							itPort->getInputRoutingData();

					ieMidSaves.append( aRoutingData.getMID() );

					if( aRoutingData.hasManyCastRoutingData() )
					{
						for( const auto & itRoutingData :
								aRoutingData.getManyCastRoutingData() )
						{
							ieMidSaves.append( itRoutingData.getMID() );
						}
					}
				}
			}

			while( writableBuffer.nonempty() )
			{
				if( ieMidComs.nonempty() )
				{
					if( ieMidComs.contains( writableBuffer.top().getMID() ) )
					{
						break;
					}
				}
				else if( ieComs->contains(writableBuffer.top().ptrPort()) )
				{
					break;
				}

				else if( ieMidSaves.nonempty() )
				{
					if( ieMidSaves.contains( writableBuffer.top().getMID() ) )
					{
						saveMessages.push_back( writableBuffer.pop() );
					}
					else
					{
						writableBuffer.pop();
					}
				}
				else
				{
					if( ieSaves->contains(writableBuffer.top().ptrPort()) )
					{
						saveMessages.push_back( writableBuffer.pop() );
					}
					else
					{
						writableBuffer.pop();
					}
				}
			}
		}

//!!! DEBUG TRACE
AVM_IF_DEBUG_FLAG_AND( STATEMENT_SCHEDULING , writableBuffer.nonempty() )
	AVM_OS_TRACE << "InputEnabled:ap> FOUND COM !!!" << std::endl;

	AVM_OS_TRACE << ieBuffer->getNameID() << ":>" << std::endl;
	writableBuffer.toFscn(AVM_OS_TRACE, tmpRID);
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_SCHEDULING )
//!!! END DEBUG TRACE

		ExecutionEnvironment tmpENV(ENV, outED, ENV.inCODE->first().bfCode());
		if( tmpENV.run() )
		{
			if( saveMessages.nonempty() )
			{
				restoreMessage(tmpRID, ieBuffer, saveMessages, tmpENV.outEDS );
				restoreMessage(tmpRID, ieBuffer, saveMessages, tmpENV.syncEDS);
				restoreMessage(tmpRID, ieBuffer, saveMessages, tmpENV.irqEDS );
				restoreMessage(tmpRID, ieBuffer, saveMessages, tmpENV.exitEDS);
			}

			ENV.spliceOutput( tmpENV );

			return( true );
		}
		else
		{
			return( false );
		}
	}
	else
	{
		return( ENV.run(ENV.inCODE->first().bfCode()) );
	}
}


void AvmPrimitive_InputEnabled::restoreMessage(
		const RuntimeID & rieRID, const InstanceOfBuffer * ieBuffer,
		ListOfMessage & saveMessages, ListOfExecutionData EDS)
{
	for( auto & itED : EDS )
	{
		itED.getWritableRuntime( rieRID ).getWritableBuffer(
				ieBuffer ).restore( saveMessages );
	}
}



} /* namespace sep */
