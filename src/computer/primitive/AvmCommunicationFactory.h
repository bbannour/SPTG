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

#ifndef AVMCOMMUNICATIONFACTORY_H_
#define AVMCOMMUNICATIONFACTORY_H_


#include <collection/Typedef.h>

#include <fml/executable/InstanceOfPort.h>

#include <fml/operator/OperatorLib.h>

#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/RuntimeID.h>


namespace sep
{

class COMPILE_CONTEXT;

class AvmCode;

class EvaluationEnvironment;
class ExecutionEnvironment;

class InstanceOfBuffer;

class Message;

class RoutingData;
class RuntimeID;


class AvmCommunicationFactory
{

private:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmCommunicationFactory()
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~AvmCommunicationFactory()
	{
		//!! NOTHING
	}


public:

	/**
	 * SEARCH ROUTING DATA
	 */
	inline static const RoutingData & searchRoutingData(
			const ExecutionData & anED, AVM_OPCODE opcode,
			const InstanceOfPort & aPort, RuntimeID & aRoutingRID )
	{
		switch( opcode )
		{
			case AVM_OPCODE_INPUT            :
			case AVM_OPCODE_INPUT_FROM       :
			case AVM_OPCODE_INPUT_ENV        :
			case AVM_OPCODE_INPUT_RDV        :
			case AVM_OPCODE_INPUT_MULTI_RDV  :
			case AVM_OPCODE_INPUT_BUFFER     :
			case AVM_OPCODE_INPUT_BROADCAST  :
			case AVM_OPCODE_INPUT_DELEGATE   :
			case AVM_OPCODE_INPUT_FLOW       :
				return( searchInputRoutingData(anED, aPort, aRoutingRID) );


			case AVM_OPCODE_OUTPUT           :
			case AVM_OPCODE_OUTPUT_TO        :
			case AVM_OPCODE_OUTPUT_ENV       :
			case AVM_OPCODE_OUTPUT_RDV       :
			case AVM_OPCODE_OUTPUT_MULTI_RDV :
			case AVM_OPCODE_OUTPUT_BUFFER    :
			case AVM_OPCODE_OUTPUT_BROADCAST :
			case AVM_OPCODE_OUTPUT_DELEGATE  :
			case AVM_OPCODE_OUTPUT_FLOW      :
				return( searchOutputRoutingData(anED, aPort, aRoutingRID) );

			default:
				return( RoutingData::nullref() );
		}
	}

	static const RoutingData & searchInputRoutingData(
			const ExecutionData & anED, const InstanceOfPort & aPort,
			RuntimeID & aRoutingRID );

	static const RoutingData & searchOutputRoutingData(
			const ExecutionData & anED, const InstanceOfPort & aPort,
			RuntimeID & aRoutingRID );

	/*
	 * CHECK ROUTING INFORMATION
	 */
	static bool isRoutingProtocolEnv(COMPILE_CONTEXT * aCTX,
			const InstanceOfPort & aPort);

	static bool isRoutingProtocolRdv(COMPILE_CONTEXT * aCTX,
			const InstanceOfPort & aPort);


	/*
	 * POP MESSAGE
	 */
	static bool popMessage(ExecutionEnvironment & ENV,
			const InstanceOfPort & aPort);

	static bool popMessage_environment(ExecutionEnvironment & ENV,
			const RuntimeID & aRoutingRID, const RoutingData & aRoutingData,
			std::size_t firstParameterOffset = 1);

	static bool popMessage_transfert(ExecutionEnvironment & ENV,
			const RuntimeID & aRoutingRID, const RoutingData & aRoutingData);

	static bool popMessage_buffer(ExecutionEnvironment & ENV,
			const RuntimeID & aRoutingRID, const RoutingData & aRoutingData);

	static bool popMessage_buffer_deterministic(
			ExecutionEnvironment & ENV, const RoutingData & aRoutingData,
			const RuntimeID & bufferDeclRID, InstanceOfBuffer & buffer);

	static bool popMessage_buffer_nondeterministic(
			ExecutionEnvironment & ENV, const RoutingData & aRoutingData,
			const RuntimeID & bufferDeclRID, InstanceOfBuffer & buffer);

	static bool popMessageManycast_buffer(ExecutionEnvironment & ENV,
			const RuntimeID & aRoutingRID, const RoutingData & aRoutingData);

	static bool popMessage_rdv(ExecutionEnvironment & ENV,
			const RuntimeID & aRoutingRID, const RoutingData & aRoutingData);


	/*
	 * POP MESSAGE FROM
	 */
	static bool popMessageFrom(ExecutionEnvironment & ENV);

	static bool popMessageFrom_transfert(
		ExecutionEnvironment & ENV, const RuntimeID & aSenderRID,
		const RuntimeID & aRoutingRID, const RoutingData & aRoutingData);

	static bool popMessageFrom_buffer(
		ExecutionEnvironment & ENV, const RuntimeID & aSenderRID,
		const RuntimeID & aRoutingRID, const RoutingData & aRoutingData);

	static bool popMessageFrom_rdv(
		ExecutionEnvironment & ENV, const RuntimeID & aSenderRID,
		const RuntimeID & aRoutingRID, const RoutingData & aRoutingData);


	/*
	 * PUSH MESSAGE
	 */
	static bool pushMessage(ExecutionEnvironment & ENV,
			const Message & anOutputMsg, RuntimeID aRoutingRID);

	static bool pushMessage_environment(
			ExecutionEnvironment & ENV, const RuntimeID & aRoutingRID,
			const RoutingData & aRoutingData, const Message & anOutputMsg);

	static bool pushMessage_transfert(
			ExecutionEnvironment & ENV, const RuntimeID & aRoutingRID,
			const RoutingData & aRoutingData, const Message & anOutputMsg);

	static bool pushMessage_buffer(
			ExecutionEnvironment & ENV, const RuntimeID & aRoutingRID,
			const RoutingData & aRoutingData, const Message & anOutputMsg);

	static bool pushMessage_rdv(
			ExecutionEnvironment & ENV, const RuntimeID & aRoutingRID,
			const RoutingData & aRoutingData, const Message & anOutputMsg);

	static bool pushMessage_broadcast(
			ExecutionEnvironment & ENV, const RuntimeID & aRoutingRID,
			const RoutingData & aRoutingData, const Message & anOutputMsg);

	static bool pushMessage_multicast(
			ExecutionEnvironment & ENV,
			const RuntimeID & aRoutingRID,
			const RoutingData & aRoutingData,
			const Message & anOutputMsg);

	static bool pushMessage_unicast(
			ExecutionEnvironment & ENV, const RuntimeID & aRoutingRID,
			const RoutingData & aRoutingData, const Message & anOutputMsg);

	static bool pushMessage_anycast(
			ExecutionEnvironment & ENV, const RuntimeID & aRoutingRID,
			const RoutingData & aRoutingData, const Message & anOutputMsg);


	/*
	 * PUSH MESSAGE TO
	 */
	static bool pushMessageTo(
			ExecutionEnvironment & ENV, const Message & anOutputMsg);

	static bool pushMessageTo_transfert(
			ExecutionEnvironment & ENV, const RuntimeID & aRoutingRID,
			const RoutingData & aRoutingData, const Message & anOutputMsg);

	static bool pushMessageTo_buffer(
			ExecutionEnvironment & ENV, const RuntimeID & aRoutingRID,
			const RoutingData & aRoutingData, const Message & anOutputMsg);

	static bool pushMessageTo_rdv(
			ExecutionEnvironment & ENV, const RuntimeID & aRoutingRID,
			const RoutingData & aRoutingData, const Message & anOutputMsg);

	static bool pushMessageTo_broadcast(
			ExecutionEnvironment & ENV, const RuntimeID & aRoutingRID,
			const RoutingData & aRoutingData, const Message & anOutputMsg);

	static bool pushMessageTo_multicast(
			ExecutionEnvironment & ENV, const RuntimeID & aRoutingRID,
			const RoutingData & aRoutingData, const Message & anOutputMsg);

	static bool pushMessageTo_unicast(
			ExecutionEnvironment & ENV, const RuntimeID & aRoutingRID,
			const RoutingData & aRoutingData, const Message & anOutputMsg);

	static bool pushMessageTo_anycast(
			ExecutionEnvironment & ENV, const RuntimeID & aRoutingRID,
			const RoutingData & aRoutingData, const Message & anOutputMsg);


	/*
	 * UPDATE BUFFER
	 */
	static bool updateBuffer(ExecutionData & anED);


	/*
	 * PRESENCE / ABSENCE status
	 */
	static bool computePresence(const ExecutionData & anED,
			const RuntimeID & aReceiverRID, const InstanceOfPort & aPort);

	static bool computePresence(const ExecutionData & anED,
			const RuntimeID & aRoutingRID, const RoutingData & aRoutingData,
			const RuntimeID & aReceiverRID, const InstanceOfPort & aPort);

	inline static bool computePresence(
			const ExecutionData & anED, const InstanceOfPort & aPort)
	{
		return( computePresence(anED, anED.getRID(), aPort) );
	}


	inline static bool computeAbsence(const ExecutionData & anED,
			const RuntimeID & aReceiverRID, const InstanceOfPort & aPort)
	{
		return( not computePresence(anED, aReceiverRID, aPort) );
	}

	inline static bool computeAbsence(
			const ExecutionData & anED, const InstanceOfPort & aPort)
	{
		return( not computePresence(anED, anED.getRID(), aPort) );
	}


	/*
	 * Collect buffer message
	 */
	static void collectBufferMessage(
			const ExecutionData & anED, BaseBufferForm & aBuffer);

};


}

#endif /* AVMCOMMUNICATIONFACTORY_H_ */
