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
	APExecutionData outED = ENV.inED;

	ListOfInstanceOfPort * ieComs  = NULL;
	ListOfInstanceOfPort * ieSaves = NULL;

	ListOfInstanceOfPort  ieMutableComs;
	ListOfInstanceOfPort  ieMutableSaves;

	// case of a composite machine
	if( outED->mRID.getExecutable()->isMutableCommunication() )
	{
		CommunicationDependency::computeInputEnabledCom((* outED), outED->mRID,
				ieMutableComs, ENV.inCODE->first().to_ptr< AvmCode >() );

		if( ieMutableComs.empty() )
		{
			return( ENV.run(ENV.inCODE->first().bfCode()) );
		}

		CommunicationDependency::computeInputEnabledSave((* outED), outED->mRID,
				ieMutableSaves, ENV.inCODE->first().to_ptr< AvmCode >() );

		ieComs  = & ieMutableComs;
		ieSaves = & ieMutableSaves;

//!!! DEBUG TRACE
AVM_IF_DEBUG_FLAG( STATEMENT_SCHEDULING )
	AVM_OS_TRACE << std::endl << "InputEnabled:mutable> " << outED->mRID.str()
			<< std::endl;
	outED->mRID.getExecutable()->getOnRun()->toStream(AVM_OS_TRACE);

	outED->mRID.getExecutable()->toStreamStaticCom(AVM_OS_TRACE);

	AVM_OS_TRACE << "com#input_enabled{" << std::endl;
	BaseCompiledForm::toStreamStaticCom(AVM_OS_TRACE, ieMutableComs);
	AVM_OS_TRACE << "}" << std::endl;

	if( ieMutableSaves.nonempty() )
	{
		AVM_OS_TRACE << "com#input_enabled#save{" << std::endl;
		BaseCompiledForm::toStreamStaticCom(AVM_OS_TRACE, ieMutableSaves);
		AVM_OS_TRACE << "}" << std::endl;
	}
AVM_ENDIF_DEBUG_FLAG( STATEMENT_SCHEDULING )
//!!! END DEBUG TRACE
	}
	else
	{
		// the expected (input) communication element
		ieComs = &(	outED->mRID.getExecutable()->getInputEnabledCom() );

		// the save (input) communication element
		ieSaves = &( outED->mRID.getExecutable()->getInputEnabledSave() );

//!!! DEBUG TRACE
AVM_IF_DEBUG_FLAG( STATEMENT_SCHEDULING )
	AVM_OS_TRACE << std::endl << "InputEnabled:final> " << outED->mRID.str()
			<< std::endl;
	outED->mRID.getExecutable()->getOnRun()->toStream(AVM_OS_TRACE);
	outED->mRID.getExecutable()->toStreamStaticCom(AVM_OS_TRACE);
AVM_ENDIF_DEBUG_FLAG( STATEMENT_SCHEDULING )
//!!! END DEBUG TRACE
	}

	ListOfMessage saveMessages;

	// the Buffer Instance
	InstanceOfBuffer * ieBuffer =
			outED->mRID.getExecutable()->getInputEnabledBuffer().front();

	// the runtime buffer machine RID
	RuntimeID tmpRID = outED->getRuntimeContainerRID(ieBuffer);

	// the runtime (reading) buffer
	const BaseBufferForm & readableBuffer =
			outED->getRuntime(tmpRID).getBuffer( ieBuffer );


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
	AVM_OS_TRACE << std::endl << "InputEnabled:av> " << outED->mRID.str()
			<< std::endl;
	outED->mRID.getExecutable()->getOnRun()->toStream(AVM_OS_TRACE);

	AVM_OS_TRACE << "com#input_enabled<mutable>{" << std::endl;
	BaseCompiledForm::toStreamStaticCom(AVM_OS_TRACE, *ieComs);
	AVM_OS_TRACE << "}" << std::endl;

	if( ieSaves->nonempty() )
	{
		AVM_OS_TRACE << "com#input_enabled#save<mutable>{" << std::endl;
		BaseCompiledForm::toStreamStaticCom(AVM_OS_TRACE, *ieSaves);
		AVM_OS_TRACE << "}" << std::endl;
	}

	AVM_OS_TRACE << ieBuffer->getNameID() << ":>" << std::endl;
	writableBuffer.toFscn(AVM_OS_TRACE, tmpRID);
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_SCHEDULING )
//!!! END DEBUG TRACE


		ListOfSizeT ieMidComs;
		RuntimeID aRoutingRID = outED->mRID;

		ListOfInstanceOfPort::const_iterator itPort = ieComs->begin();
		ListOfInstanceOfPort::const_iterator enItPort = ieComs->end();
		for( ; itPort != enItPort ; ++itPort )
		{
			if( (*itPort)->hasInputRoutingData() )
			{
				ieMidComs.append( (*itPort)->getInputRoutingData().getMID() );
			}
			else
			{
				const RoutingData & aRoutingData = AvmCommunicationFactory::
					searchInputRoutingData( outED, (*itPort), aRoutingRID );
				if( aRoutingData.valid() )
				{
					ieMidComs.append( aRoutingData.getMID() );
				}
			}
		}

		if( ieSaves->empty() )
		{
			if( ieMidComs.nonempty() )
			{
				writableBuffer.popBefore( ieMidComs , outED->mRID);
			}
			else if( (*ieComs).nonempty() )
			{
				writableBuffer.popBefore( *ieComs , outED->mRID);
			}
			else
			{
				writableBuffer.popBefore( outED->mRID);
			}
		}
		else
		{
			ListOfSizeT ieMidSaves;
			enItPort = ieSaves->end();
			for( itPort = ieSaves->begin() ; itPort != enItPort ; ++itPort )
			{
				if( (*itPort)->hasInputRoutingData() )
				{
					ieMidSaves.append(
							(*itPort)->getInputRoutingData().getMID() );
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
				else if( ieComs->contains( writableBuffer.top().getPort() ) )
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
					if( ieSaves->contains( writableBuffer.top().getPort() ) )
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

		if( writableBuffer.nonempty() )
		{
//!!! DEBUG TRACE
AVM_IF_DEBUG_FLAG( STATEMENT_SCHEDULING )
	AVM_OS_TRACE << "InputEnabled:ap> FOUND COM !!!" << std::endl;

	AVM_OS_TRACE << ieBuffer->getNameID() << ":>" << std::endl;
	writableBuffer.toFscn(AVM_OS_TRACE, tmpRID);
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_SCHEDULING )
//!!! END DEBUG TRACE
		}

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
		const RuntimeID & rieRID, InstanceOfBuffer * ieBuffer,
		ListOfMessage & saveMessages, ListOfAPExecutionData EDS)
{
	ListOfAPExecutionData::iterator itED = EDS.begin();
	ListOfAPExecutionData::iterator endED = EDS.end();
	for( ; itED != endED ; ++itED )
	{
		(*itED).getWritableRuntime( rieRID ).getWritableBuffer(
				ieBuffer ).restore( saveMessages );
	}
}



} /* namespace sep */
