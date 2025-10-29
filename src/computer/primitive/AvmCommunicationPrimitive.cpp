/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 20 mai 2010
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmCommunicationPrimitive.h"

#include <builder/Builder.h>

#include <computer/EvaluationEnvironment.h>
#include <computer/ExecutionDataFactory.h>
#include <computer/ExecutionEnvironment.h>
#include <computer/PathConditionProcessor.h>

#include <computer/primitive/AvmCommunicationFactory.h>
#include <computer/primitive/AvmAssignPrimitive.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/ExpressionConstant.h>
#include <fml/expression/ExpressionSimplifier.h>
#include <fml/expression/StatementConstructor.h>

#include <fml/runtime/ExecutionConfiguration.h>
#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/RuntimeLib.h>
#include <fml/runtime/RuntimeID.h>


namespace sep
{


/**
 ***************************************************************************
 * execution of an INPUT program
 ***************************************************************************
 */

bool AvmPrimitive_Input::run(ExecutionEnvironment & ENV)
{
AVM_IF_DEBUG_FLAG_AND_NOT_FLAG( COMMUNICATION , STATEMENT )
	AVM_OS_TRACE << TAB << "Input Message to receive: "
			<< ENV.inCODE->str() << std::endl;
AVM_ENDIF_DEBUG_FLAG_AND_NOT_FLAG( COMMUNICATION , STATEMENT )

	if( not AvmCommunicationFactory::popMessage(ENV,
			ENV.mARG->at(0).to< InstanceOfPort >()) )
	{
AVM_IF_DEBUG_FLAG( STATEMENT)
	AVM_OS_TRACE << TAB << "THROW UNSATISFIED << INPUT >> :> "
			<< ENV.mARG->outED.getRID().strUniqId()
			<< " |=> " << ENV.inCODE->str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT)
	}

	return( true );
}


bool AvmPrimitive_InputVar::run(ExecutionEnvironment & ENV)
{
	InstanceOfData & anInstance = ENV.mARG->at(0).to< InstanceOfData >();

	BFList paramList;
	BF aNewSymbolicConstant( ENV.createNewFreshParam(ENV.mARG->outED.getRID(),
			anInstance, paramList) );

	ExecutionDataFactory::appendIOElementTrace(ENV.mARG->outED,
			BF( new ExecutionConfiguration(ENV.mARG->outED.getRID(),
					BFCode(OperatorManager::OPERATOR_INPUT_VAR,
								ENV.mARG->at(0), aNewSymbolicConstant),
					ENV.mARG->outED.getTimeValue(ENV.mARG->outED.getRID()) )));

	if( ENV.setRvalue(ENV.mARG->outED, anInstance, aNewSymbolicConstant) )
	{
		ENV.mARG->outED.appendParameters( paramList );

		ENV.appendOutput( ENV.mARG->outED );

		return( true );
	}

	return( false );
}


bool AvmPrimitive_InputEnv::run(ExecutionEnvironment & ENV)
{
	BFCode aTraceInput(OperatorManager::OPERATOR_INPUT_ENV, ENV.mARG->at(0));

	bool allSuccess = true;

	if( ENV.inCODE->hasManyOperands() )
	{
		ENV.mARG->outED.makeModifiableParamTable();

		const InstanceOfPort & aPort = ENV.mARG->at(0).to< InstanceOfPort >();
		std::size_t offset = 0;

		BF aNewSymbolicConstant;
		BFList paramList;

		for( ENV.mARG->begin(1) ; ENV.mARG->hasNext() ;
				ENV.mARG->next() , ++offset )
		{
			paramList.clear();

			InstanceOfData & aVar = ENV.mARG->current().to< InstanceOfData >();

			aNewSymbolicConstant = ENV.createNewFreshParam(
					ENV.mARG->outED.getRID(), aPort.getParameterType(offset),
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
						ENV.mARG->outED.getRID(), aTraceInput,
						ENV.mARG->outED.getTimeValue(
								ENV.mARG->outED.getRID()) )));

		ENV.outEDS.append( ENV.mARG->outED );

		return( true );
	}
	else
	{
		return( false );
	}
}


bool AvmPrimitive_InputBuffer::run(ExecutionEnvironment & ENV)
{
AVM_IF_DEBUG_FLAG( STATEMENT_COMMUNICATION )
	AVM_OS_TRACE << TAB << "begin AvmPrimitive_InputBuffer::run" << std::endl;

	ENV.mARG->outED.getRuntime(1).toStreamData(
			ENV.mARG->outED, AVM_OS_TRACE << INCR2_INDENT_TAB);
	AVM_OS_TRACE << DECR2_INDENT;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_COMMUNICATION )


	const RoutingData & aRoutingData =
			ENV.mARG->at(0).to< InstanceOfPort >().getInputRoutingData();

	const RuntimeID & aRoutingRID = aRoutingData.getRuntimeRID();

	RuntimeID bufferDeclRID = aRoutingRID;

	InstanceOfBuffer * aBuffer = aRoutingData.getBufferInstance().first();

	bufferDeclRID = ENV.mARG->outED.getRuntimeContainerRID(
			ENV.mARG->outED.getRID(), aBuffer);
	if( bufferDeclRID.valid() )
	{
		BaseBufferForm & bbf =
				ENV.mARG->outED.getWritableRuntime(
						bufferDeclRID ).getWritableBuffer( aBuffer );

		Message popMsg;
/*!!INPUT#ENABLED!!
		if( ENV.mARG->outED.getRuntime(ENV.mARG->outED.getRID()).isInputEnabled()
			|| ENV.mARG->outED.getRuntime(aRoutingRID).isInputEnabled()
			|| aRoutingData.isInputEnabled() || bbf->isInputEnabled() )
		{
			popMsg = bbf->popUntil(aRoutingData.getMID());
		}
		else*/
		{
			popMsg = bbf.pop(aRoutingData.getMID(), ENV.mARG->outED.getRID());
		}

		if( popMsg.valid() )
		{
			BFCode aTraceInput(OperatorManager::OPERATOR_INPUT, ENV.mARG->at(0));

			Message::const_iterator itVal = popMsg.beginParameters();
			Message::const_iterator endVal = popMsg.endParameters();

			// We have to ignore the << Port >> InstanceOfPort
			for( ENV.mARG->begin(1) ; (itVal != endVal) && ENV.mARG->hasNext() ;
					ENV.mARG->next() , ++itVal )
			{
				if( ENV.setRvalue(ENV.mARG->outED,
						ENV.mARG->current().to< InstanceOfData >(), *itVal) )
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
							ENV.mARG->outED.getRID(), aTraceInput, popMsg,
							ENV.mARG->outED.getTimeValue(
									ENV.mARG->outED.getRID()) )));

			ENV.outEDS.append( ENV.mARG->outED );

AVM_IF_DEBUG_FLAG( STATEMENT_COMMUNICATION )
	ENV.mARG->outED.getRuntime(1).toStreamData(
			ENV.mARG->outED, AVM_OS_TRACE << INCR2_INDENT_TAB);

	AVM_OS_TRACE << DECR2_INDENT_TAB
			<< "end AvmPrimitive_InputBuffer::run"
			<< std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_COMMUNICATION )

			return( true );
		}
	}

	return( false );
}


bool AvmPrimitive_InputRdv::run(ExecutionEnvironment & ENV)
{
	const BF & aPort = ENV.mARG->at(0);

	const RoutingData & aRoutingData =
			aPort.to< InstanceOfPort >().getInputRoutingData();

	const RuntimeID & aRoutingRID = aRoutingData.getRuntimeRID();

	Message inMsg( aRoutingData,
			RuntimeID::nullref(), ENV.mARG->outED.getRID(), aPort );

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



/**
 ***************************************************************************
 * execution of an INPUT_FROM program
 ***************************************************************************
 */
bool AvmPrimitive_InputFrom::run(ExecutionEnvironment & ENV)
{
AVM_IF_DEBUG_FLAG_AND_NOT_FLAG( COMMUNICATION , STATEMENT )
	AVM_OS_TRACE << TAB << "Input Message to receive: "
			<< ENV.inCODE->str() << std::endl;
AVM_ENDIF_DEBUG_FLAG_AND_NOT_FLAG( COMMUNICATION , STATEMENT )

	if( (RuntimeLib::RID_ENVIRONMENT == ENV.mARG->at(1))
		|| (RuntimeLib::RID_NIL == ENV.mARG->at(1)) )
	{
		AvmCommunicationFactory::popMessage_environment(ENV,
				ENV.mARG->at(1).bfRID(), RoutingData::nullref(), 2);
	}
	else if( not AvmCommunicationFactory::popMessageFrom(ENV) )
	{
AVM_IF_DEBUG_FLAG( STATEMENT)
	AVM_OS_TRACE << TAB << "THROW UNSATISFIED << INPUT#FROM >> :> ?!? |=> "
			<< ENV.inCODE->str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT)
	}

	return( true );
}


/**
 ***************************************************************************
 * execution of an OUTPUT program
 ***************************************************************************
 */

bool AvmPrimitive_Output::run(ExecutionEnvironment & ENV)
{
AVM_IF_DEBUG_FLAG_AND_NOT_FLAG( COMMUNICATION , STATEMENT )
	AVM_OS_TRACE << INCR_INDENT_TAB
			<< "<!?!" << ENV.inED.getRID().strUniqId()
			<< " |=> " << ENV.inCODE->str() << std::endl;
AVM_ENDIF_DEBUG_FLAG_AND_NOT_FLAG( COMMUNICATION , STATEMENT )

	Message anOutputMsg( ENV.mARG->outED.getRID(), ENV.mARG->at(0) );

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , STATEMENT_COMMUNICATION )
	AVM_OS_TRACE << TAB << "Output Message to build" << std::endl;
	anOutputMsg.toStream(AVM_OS_TRACE);
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , STATEMENT_COMMUNICATION )


	for( ENV.mARG->begin(1) ; ENV.mARG->hasNext() ; ENV.mARG->next() )
	{
		anOutputMsg.appendParameter( ENV.mARG->current() );
	}


AVM_IF_DEBUG_FLAG( STATEMENT_COMMUNICATION )
	AVM_OS_TRACE << TAB << "Output Message to push" << std::endl;
	anOutputMsg.toStream(AVM_OS_TRACE);
AVM_ENDIF_DEBUG_FLAG( STATEMENT_COMMUNICATION )


	if( not AvmCommunicationFactory::pushMessage(ENV,
			anOutputMsg, ENV.mARG->outED.getRID()) )
	{
AVM_IF_DEBUG_FLAG( STATEMENT)
	AVM_OS_TRACE << TAB << "THROW UNSATISFIED << OUTPUT >> : <<< "
			<< ENV.mARG->outED.getRID().strUniqId()
			<< " |=> " << ENV.inCODE->str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT)
	}


AVM_IF_DEBUG_FLAG( STATEMENT_COMMUNICATION )
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< "!?!> " << ENV.inED.getRID().strUniqId()
			<< " |=> " <<  ENV.inCODE->str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_COMMUNICATION )

	return( true );
}


bool AvmPrimitive_OutputVar::run(ExecutionEnvironment & ENV)
{
	ExecutionDataFactory::appendIOElementTrace(ENV.mARG->outED,
			BF( new ExecutionConfiguration(ENV.mARG->outED.getRID(),
					BFCode(OperatorManager::OPERATOR_OUTPUT_VAR,
							ENV.mARG->at(0), ENV.mARG->at(1)),
					ENV.mARG->outED.getTimeValue(ENV.mARG->outED.getRID()) )));

	ENV.appendOutput( ENV.mARG->outED );

	return( true );
}


bool AvmPrimitive_OutputEnv::run(ExecutionEnvironment & ENV)
{
	BFCode aTraceOutput(OperatorManager::OPERATOR_OUTPUT_ENV, ENV.mARG->at(0));

	for( ENV.mARG->begin(1) ; ENV.mARG->hasNext() ; ENV.mARG->next() )
	{
		aTraceOutput->append( ENV.mARG->current() );
	}

	ExecutionDataFactory::appendIOElementTrace(ENV.mARG->outED,
			BF( new ExecutionConfiguration(
					ENV.mARG->outED.getRID(), aTraceOutput,
					ENV.mARG->outED.getTimeValue(ENV.mARG->outED.getRID()) )));

	ENV.outEDS.append( ENV.mARG->outED );

	return( true );
}


bool AvmPrimitive_OutputBuffer::run(ExecutionEnvironment & ENV)
{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , STATEMENT_COMMUNICATION )
	AVM_OS_TRACE << TAB << "begin AvmPrimitive_OutputBuffer::run" << std::endl;

	ENV.mARG->outED.getRuntime(1).toStream(
			AVM_OS_TRACE << INCR2_INDENT_TAB);
	AVM_OS_TRACE << DECR2_INDENT;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , STATEMENT_COMMUNICATION )

	const BF & aPort = ENV.mARG->at(0);

	const RoutingData & aRoutingData =
			aPort.to< InstanceOfPort >().getOutputRoutingData();

	const RuntimeID & aRoutingRID = aRoutingData.getRuntimeRID();

	RuntimeID bufferDeclRID = aRoutingRID;

	const InstanceOfBuffer * aBuffer = aRoutingData.getBufferInstance().first();

	bufferDeclRID = ENV.mARG->outED.getRuntimeContainerRID(
			ENV.mARG->outED.getRID(), aBuffer);

	if( bufferDeclRID.valid() )
	{
		BaseBufferForm & bbf =
				ENV.mARG->outED.getWritableRuntime(
						bufferDeclRID ).getWritableBuffer( aBuffer );

		Message outMsg( aRoutingData,
				ENV.mARG->outED.getRID(), ENV.mARG->outED.getRID(), aPort );

		// We have to ignore the << Port >> InstanceOfPort
		for( ENV.mARG->begin(1) ; ENV.mARG->hasNext() ; ENV.mARG->next() )
		{
			outMsg.appendParameter( ENV.mARG->current() );
		}

		if( bbf.push( outMsg ) )
		{
			BFCode aTraceOutput(OperatorManager::OPERATOR_OUTPUT, aPort);

			aTraceOutput->append( outMsg.getParameters() );

			ExecutionDataFactory::appendIOElementTrace(ENV.mARG->outED,
					BF( new ExecutionConfiguration(
							ENV.mARG->outED.getRID(), aTraceOutput, outMsg,
							ENV.mARG->outED.getTimeValue(
									ENV.mARG->outED.getRID()) )));

			ENV.outEDS.append( ENV.mARG->outED );


AVM_IF_DEBUG_LEVEL_FLAG( HIGH , STATEMENT_COMMUNICATION )
	ENV.mARG->outED.getRuntime(1).toStream(
			AVM_OS_TRACE << INCR2_INDENT_TAB);

	AVM_OS_TRACE << DECR2_INDENT_TAB
			<< "end AvmPrimitive_OutputBuffer::run"
			<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , STATEMENT_COMMUNICATION )

			return( true );
		}
	}

	return( false );
}


bool AvmPrimitive_OutputRdv::run(ExecutionEnvironment & ENV)
{
	const BF & aPort = ENV.mARG->at(0);

	const RoutingData & aRoutingData =
			aPort.to< InstanceOfPort >().getOutputRoutingData();

	const RuntimeID & aRoutingRID = aRoutingData.getRuntimeRID();

	Message outMsg( aRoutingData,
			ENV.mARG->outED.getRID(), ENV.mARG->outED.getRID(), aPort );

	// We have to ignore the << Port >> InstanceOfPort
	for( ENV.mARG->begin(1) ; ENV.mARG->hasNext() ; ENV.mARG->next() )
	{
		outMsg.appendParameter( ENV.mARG->current() );
	}

	ENV.mARG->outED.pushExecSyncPoint(new ExecutionSynchronizationPoint(
			AWAITING_POINT_OUTPUT_NATURE, aRoutingRID, aRoutingData, outMsg) );

	ENV.appendSync_mwsetAEES(ENV.mARG->outED, AEES_WAITING_OUTCOM_RDV);

	return( true );
}


/**
 ***************************************************************************
 * execution of an OUTPUT_TO program
 ***************************************************************************
 */
bool AvmPrimitive_OutputTo::run(ExecutionEnvironment & ENV)
{
AVM_IF_DEBUG_FLAG_AND_NOT_FLAG( COMMUNICATION , STATEMENT )
	AVM_OS_TRACE << INCR_INDENT_TAB
			<< "<!?!" << ENV.inED.getRID().strUniqId()
			<< " |=> " << ENV.inCODE->str() << std::endl;
AVM_ENDIF_DEBUG_FLAG_AND_NOT_FLAG( COMMUNICATION , STATEMENT )

	Message anOutputMsg( ENV.mARG->outED.getRID(),
			ENV.mARG->at(0), ENV.mARG->at(1).bfRID() );

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , STATEMENT_COMMUNICATION )
	AVM_OS_TRACE << TAB << "Output Message to build" << std::endl;
	anOutputMsg.toStream(AVM_OS_TRACE);
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , STATEMENT_COMMUNICATION )


	for( ENV.mARG->begin(2) ; ENV.mARG->hasNext() ; ENV.mARG->next() )
	{
		anOutputMsg.appendParameter( ENV.mARG->current() );
	}


AVM_IF_DEBUG_FLAG( STATEMENT_COMMUNICATION )
	AVM_OS_TRACE << TAB << "Output Message to push" << std::endl;
	anOutputMsg.toStream(AVM_OS_TRACE);
AVM_ENDIF_DEBUG_FLAG( STATEMENT_COMMUNICATION )


	if( ENV.mARG->at(0).to< InstanceOfPort >().isPort() )
	{
		if( not AvmCommunicationFactory::pushMessageTo(ENV, anOutputMsg) )
		{
AVM_IF_DEBUG_FLAG( STATEMENT)
	AVM_OS_TRACE << TAB << "THROW UNSATISFIED << OUTPUT >> : <<< "
			<< ENV.mARG->outED.getRID().strUniqId()
			<< " |=> " << ENV.inCODE->str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT)
		}
	}
	else// if( ENV.mARG->at(0).to< InstanceOfPort >().isSignal() )
	{
		if( ENV.mARG->at(1).bfRID().valid() )
		{
			if( (RuntimeLib::RID_ENVIRONMENT == ENV.mARG->at(1))
				|| (RuntimeLib::RID_NIL == ENV.mARG->at(1)) )
			{
				AvmCommunicationFactory::pushMessage_environment(ENV,
					ENV.mARG->at(1).bfRID(), RoutingData::nullref(), anOutputMsg);
			}
			else if( not AvmCommunicationFactory::pushMessage(ENV,
					anOutputMsg, ENV.mARG->at(1).bfRID()) )
			{
AVM_IF_DEBUG_FLAG( STATEMENT)
	AVM_OS_TRACE << TAB << "THROW UNSATISFIED << OUTPUT#TO<"
			<< ENV.mARG->at(1).bfRID().getFullyQualifiedNameID() << "> >> : <<< "
			<< ENV.mARG->outED.getRID().strUniqId()
			<< " |=> " << ENV.inCODE->str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT)
			}
		}
		else
		{
AVM_IF_DEBUG_FLAG( STATEMENT)
	AVM_OS_TRACE << TAB << "THROW UNKNOWN RECEIVER << OUTPUT#TO<"
			<< ENV.mARG->at(1).bfRID().getFullyQualifiedNameID() << "?> >> : <<< "
			<< ENV.mARG->outED.getRID().strUniqId()
			<< " |=> " << ENV.inCODE->str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT)

			return( false );
		}
	}

AVM_IF_DEBUG_FLAG( STATEMENT_COMMUNICATION )
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< "!?!> " << ENV.inED.getRID().strUniqId()
			<< " |=> " <<  ENV.inCODE->str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_COMMUNICATION )

	return( true );
}


/**
 ***************************************************************************
 * execution of a PRESENT program
 ***************************************************************************
 */
bool AvmPrimitive_Present::run(ExecutionEnvironment & ENV)
{
	if( AvmCommunicationFactory::computePresence(ENV.mARG->outED,
			ENV.mARG->at(0).to< InstanceOfPort >()) )
	{
		ENV.outEDS.append( ENV.mARG->outED );
	}
	else
	{
AVM_IF_DEBUG_FLAG( STATEMENT)
	AVM_OS_TRACE << "THROW UNSATISFIED << PRESENCE >> :> ?!? < "
			<< ENV.inCODE->str() << " >|=> "
			<< ENV.mARG->at(0).str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT)
	}

	return( true );
}


bool AvmPrimitive_Present::seval(EvaluationEnvironment & ENV)
{
	ENV.outVAL = ExpressionConstructor::newBoolean(
			AvmCommunicationFactory::computePresence(ENV.mARG->outED,
					ENV.mARG->at(0).to< InstanceOfPort >()) );

	return( true );
}



/**
 ***************************************************************************
 * execution of an ABSENT program
 ***************************************************************************
 */
bool AvmPrimitive_Absent::run(ExecutionEnvironment & ENV)
{
	if( AvmCommunicationFactory::computeAbsence(ENV.mARG->outED,
			ENV.mARG->at(0).to< InstanceOfPort >()) )
	{
		ENV.outEDS.append( ENV.mARG->outED );
	}
	else
	{
AVM_IF_DEBUG_FLAG( STATEMENT)
	AVM_OS_TRACE << "THROW UNSATISFIED << ABSENCE >> :> ?!? < "
			<< ENV.inCODE->str() << " >|=> "
			<< ENV.mARG->at(0).str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT)
	}

	return( true );
}


bool AvmPrimitive_Absent::seval(EvaluationEnvironment & ENV)
{
	ENV.outVAL = ExpressionConstructor::newBoolean(
			AvmCommunicationFactory::computeAbsence(ENV.mARG->outED,
					ENV.mARG->at(0).to< InstanceOfPort >()) );

	return( true );
}



/**
 ***************************************************************************
 * execution of a UPDATE BUFFER program
 ***************************************************************************
 */
bool AvmPrimitive_UpdateBuffer::run(ExecutionEnvironment & ENV)
{
	if( ENV.inCODE->size() == 1 )
	{
		switch( ENV.inCODE->first().classKind() )
		{
			case FORM_AVMCODE_KIND:
			{
				ExecutionEnvironment tmpENV(ENV, ENV.inCODE->first());
				if( tmpENV.run() )
				{
					ExecutionData tmpED;
					while( tmpENV.outEDS.nonempty() )
					{
						tmpENV.outEDS.pop_first_to( tmpED );

						if( AvmCommunicationFactory::updateBuffer(tmpED) )
						{
							ENV.outEDS.append( tmpED );
						}
					}

					ENV.spliceOutput(tmpENV);

					return( true );
				}

				break;
			}

			default:
			{
				AVM_OS_WARNING_ALERT
						<< "Unexpected argument KIND for an SYNCHRONIZE program\n"
						<< ENV.inCODE->toString( AVM_TAB1_INDENT )
						<< SEND_ALERT;

				return( false );
			}
		}
	}
	else
	{
		ExecutionData anOutputED = ENV.inED;
		if( AvmCommunicationFactory::updateBuffer(anOutputED) )
		{
			ENV.outEDS.append( anOutputED );

			return( true );
		}
	}

	return( false );
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// MATH MIN
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmPrimitive_OBS::run(ExecutionEnvironment & ENV)
{
	if( ENV.mARG->at(2).isEqualTrue()  )
	{
		//!! NO NEED PATH CONDITION UPDATE
		ENV.appendOutput( ENV.mARG->outED );
	}

	else if( ENV.mARG->at(2).isEqualFalse()  )
	{
AVM_IF_DEBUG_FLAG( STATEMENT)
	AVM_OS_TRACE << "THROW UNSATISFIED << OBS >> POST CONDITION : "
			<< ENV.mARG->outED.getRID().strUniqId() << " |=> "
			<< ENV.inCODE->str() << std::endl;
//	AVM_OS_TRACE << "THROW UNSATISFIED << GUARD >> : "
//			<< ENV.mARG->outED.getRID().strUniqId() << " , ";
//	AVM_OS_TRACE << ENV.inCODE->str()  << " |=> "
//			<< ENV.mARG->at(2).str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT)
	}

	else
	{
		AVM_OS_TRACE << "OBS :> " << ENV.mARG->at(2).str() << std::endl;

		if( not PathConditionProcessor::appendPathCondition(
				ENV, ENV.mARG->outED, ENV.mARG->at(2)) )
		{
AVM_IF_DEBUG_FLAG( STATEMENT)
	AVM_OS_TRACE << "THROW UNSATISFIED << OBS >> POST CONDITION : "
			<< ENV.mARG->outED.getRID().strUniqId() << " |=> "
			<< ENV.inCODE->str() << std::endl;
//	AVM_OS_TRACE << "THROW UNSATISFIED << GUARD >> : "
//			<< ENV.mARG->outED.getRID().strUniqId() << " , ";
//	AVM_OS_TRACE << ENV.inCODE->str()  << " |=> "
//			<< ENV.mARG->at(2).str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT)
		}
	}

	return( true );
}

bool AvmPrimitive_OBS::seval(EvaluationEnvironment & ENV)
{
	if( ENV.mARG->at(0).is< AvmCode >() )
	{
		const AvmCode & evtCondition = ENV.mARG->at(0).to< AvmCode >();

		switch( evtCondition.getAvmOpCode() )
		{
			case AVM_OPCODE_INPUT:
			case AVM_OPCODE_OUTPUT:
			{
				if( evtCondition.first().is< BaseInstanceForm >() )
				{
					const BaseInstanceForm & ioInstance =
							evtCondition.first().to< BaseInstanceForm >();

					if( ioInstance.is< InstanceOfPort >() )
					{
						AvmCode * ioTrace = ENV.searchTraceIO(
								ENV.outED.getIOElementTrace(), evtCondition);

						if( ioTrace != nullptr )
						{
							ENV.outVAL = ENV.ioSubst( ENV.outED,
									ENV.outED.getRID().getExecutable(),
									evtCondition, *ioTrace, ENV.mARG->at(1) );
						}
						else
						{
							ENV.outVAL = ExpressionConstant::BOOLEAN_FALSE;
						}

						return( true );
					}
					else if( ioInstance.is< InstanceOfData >() )
					{
						if( ENV.isAssigned(ENV.outED, ENV.outED.getRID(),
								ioInstance.to< InstanceOfData >()) )
						{
							if( not ENV.seval(ENV.mARG->at(1)) )
							{
								return( false );
							}
						}
						else
						{
							ENV.outVAL = ExpressionConstant::BOOLEAN_FALSE;
						}

						return( true );
					}
				}

				ENV.outVAL = ExpressionConstant::BOOLEAN_FALSE;

				return( true );
			}

			default:
			{
				BF evtCond = ENV.outVAL;

				if( ENV.seval(ENV.mARG->at(1)) )
				{
					ENV.outVAL = ExpressionSimplifier::AND(
							ENV.mARG->at(0), evtCond);

					return( true );
				}
				break;
			}
		}
	}

	else if( ENV.mARG->at(0).isEqualTrue() )
	{
		return( ENV.seval(ENV.mARG->at(1)) );
	}
	else if( ENV.mARG->at(0).isNotEqualFalse() )
	{
		BF evtCond = ENV.outVAL;
		if( ENV.seval(ENV.mARG->at(1)) )
		{
			ENV.outVAL = ExpressionSimplifier::AND(ENV.mARG->at(0), evtCond);

			return( true );
		}
	}

	return( false );
}



}
