/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 24 févr. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef COMMUNICATIONDEPENDENCY_H_
#define COMMUNICATIONDEPENDENCY_H_

#include <common/BF.h>

#include <fml/expression/AvmCode.h>

#include <fml/executable/AvmProgram.h>

#include <fml/operator/OperatorLib.h>


namespace sep
{


class ExecutionData;


class CommunicationDependency
{

public:

	/**
	 * Collect information about
	 * general communication
	 */
	static BF getCommunicationCode(
			AvmProgram * anAvmProgram, const BFCode & aCode,
			bool (*isCom)(AvmCode * comCode) , bool & hasMutableSchedule );


	static bool isCommunicationCode(AvmCode * comCode)
	{
		AVM_OPCODE opCode = comCode->getAvmOpCode();

		return( (opCode == AVM_OPCODE_INPUT      ) ||
				(opCode == AVM_OPCODE_INPUT_FROM ) ||
				(opCode == AVM_OPCODE_OUTPUT     ) ||
				(opCode == AVM_OPCODE_OUTPUT_TO  ) );
	}

	inline static BF getCommunicationCode(AvmProgram * anAvmProgram,
			const BFCode & aCode, bool & hasMutableSchedule)
	{
		return( getCommunicationCode(anAvmProgram, aCode,
				& CommunicationDependency::isCommunicationCode,
				hasMutableSchedule) );
	}


	static bool isInternalCommunicationCode(AvmCode * comCode)
	{
		AVM_OPCODE opCode = comCode->getAvmOpCode();
		AVM_OPCODE optimizCode = comCode->getOptimizedOpCode();

		return( ((opCode == AVM_OPCODE_INPUT     ) ||
				(opCode == AVM_OPCODE_INPUT_FROM ) ||
				(opCode == AVM_OPCODE_OUTPUT     ) ||
				(opCode == AVM_OPCODE_OUTPUT_TO  ) )  &&
				(optimizCode != AVM_OPCODE_INPUT_ENV) &&
				(optimizCode != AVM_OPCODE_OUTPUT_ENV) );
	}

	inline static BF getInternalCommunicationCode(AvmProgram * anAvmProgram,
			const BFCode & aCode, bool & hasMutableSchedule)
	{
		return( getCommunicationCode(anAvmProgram, aCode,
				& CommunicationDependency::isInternalCommunicationCode,
				hasMutableSchedule) );
	}


	/**
	 * Collect information about
	 * communication with the environment
	 */
	static bool isEnvironmentCom(AvmCode * comCode)
	{
		AVM_OPCODE optimizeCode = comCode->getOptimizedOpCode();

		return( (optimizeCode == AVM_OPCODE_INPUT_ENV) ||
				(optimizeCode == AVM_OPCODE_OUTPUT_ENV) );
	}

	inline static BF getEnvironmentCom(AvmProgram * anAvmProgram,
			const BFCode & aCode, bool & hasMutableSchedule)
	{
		return( getCommunicationCode(anAvmProgram, aCode,
				& CommunicationDependency::isEnvironmentCom,
				hasMutableSchedule) );
	}



	static bool isEnvironmentInputCom(AvmCode * comCode)
	{
		return( comCode->getOptimizedOpCode() == AVM_OPCODE_INPUT_ENV );
	}

	inline static BF getEnvironmentInputCom(AvmProgram * anAvmProgram,
			const BFCode & aCode, bool & hasMutableSchedule)
	{
		return( getCommunicationCode(anAvmProgram, aCode,
				& CommunicationDependency::isEnvironmentInputCom,
				hasMutableSchedule) );
	}


	static bool isEnvironmentOutputCom(AvmCode * comCode)
	{
		return( comCode->getOptimizedOpCode() == AVM_OPCODE_OUTPUT_ENV );
	}

	inline static BF getEnvironmentOutputCom(AvmProgram * anAvmProgram,
			const BFCode & aCode, bool & hasMutableSchedule)
	{
		return( getCommunicationCode(anAvmProgram, aCode,
				& CommunicationDependency::isEnvironmentOutputCom,
				hasMutableSchedule) );
	}



	/**
	 * Collect information about
	 * static input enabled communication
	 */
	static void computeInputEnabledCom(AvmProgram * anAvmProgram,
			ListOfInstanceOfPort & inputEnabledCom, AvmCode * aCode,
			bool (*isCom)(AvmCode * comCode) , bool & hasMutableSchedule );


	static bool isInputEnabledCom(AvmCode * comCode)
	{
		return( (comCode->hasOpCode( AVM_OPCODE_INPUT, AVM_OPCODE_INPUT_FROM ))
				&& (comCode->getOptimizedOpCode() != AVM_OPCODE_INPUT_ENV) );
	}

	inline static void computeInputEnabledCom(
			AvmProgram * anAvmProgram, AvmCode * aCode)
	{
		bool hasMutableSchedule = false;

		computeInputEnabledCom( anAvmProgram,
				anAvmProgram->getInputEnabledCom(), aCode,
				& CommunicationDependency::isInputEnabledCom,
				hasMutableSchedule );

		anAvmProgram->setMutableCommunication( hasMutableSchedule );
	}


	static bool isInputEnabledSave(AvmCode * comCode)
	{
		return( comCode->isOpCode( AVM_OPCODE_INPUT_SAVE ) );
	}

	inline static void computeInputEnabledSave(
			AvmProgram * anAvmProgram, AvmCode * aCode)
	{
		bool hasMutableSchedule = false;

		computeInputEnabledCom( anAvmProgram,
				anAvmProgram->getInputEnabledSave(), aCode,
				& CommunicationDependency::isInputEnabledSave,
				hasMutableSchedule );

		anAvmProgram->setMutableCommunication( hasMutableSchedule );
	}



	/**
	 * Collect information about
	 * input / output internal communication
	 */
	static bool isInputCom(AvmCode * comCode)
	{
		return( (comCode->hasOpCode( AVM_OPCODE_INPUT, AVM_OPCODE_INPUT_FROM ))
				&& (comCode->getOptimizedOpCode() != AVM_OPCODE_INPUT_ENV) );
	}

	inline static BF getInputCom(AvmProgram * anAvmProgram,
			const BFCode & aCode, bool & hasMutableSchedule)
	{
		return( getCommunicationCode(anAvmProgram, aCode,
				& CommunicationDependency::isInputCom, hasMutableSchedule) );
	}

	static void computeInputCom(AvmProgram * anAvmProgram, AvmCode * aCode)
	{
		bool hasMutableSchedule = false;

		computeInputEnabledCom(anAvmProgram, anAvmProgram->getInputCom(), aCode,
				& CommunicationDependency::isInputCom, hasMutableSchedule);

		anAvmProgram->setMutableCommunication( hasMutableSchedule );
	}


	static bool isOutputCom(AvmCode * comCode)
	{
		return( (comCode->hasOpCode( AVM_OPCODE_OUTPUT, AVM_OPCODE_OUTPUT_TO ))
				&& (comCode->getOptimizedOpCode() != AVM_OPCODE_OUTPUT_ENV) );
	}

	inline static BF getOutputCom(AvmProgram * anAvmProgram,
			const BFCode & aCode, bool & hasMutableSchedule)
	{
		return( getCommunicationCode(anAvmProgram, aCode,
				& CommunicationDependency::isOutputCom, hasMutableSchedule) );
	}


	static void computeOutputCom( AvmProgram * anAvmProgram, AvmCode * aCode)
	{
		bool hasMutableSchedule = false;

		computeInputEnabledCom(anAvmProgram, anAvmProgram->getOutputCom(), aCode,
				& CommunicationDependency::isOutputCom, hasMutableSchedule);

		anAvmProgram->setMutableCommunication( hasMutableSchedule );
	}



	/**
	 * Collect information about
	 * runtime input enabled communication
	 */
	static void computeInputEnabledCom(const ExecutionData & anED,
			const RuntimeID & aRID, ListOfInstanceOfPort & inputEnabledCom,
			AvmCode * aCode, bool (*isCom)(AvmCode * comCode) );


	inline static void computeInputEnabledCom(
			const ExecutionData & anED, const RuntimeID & aRID,
			ListOfInstanceOfPort & inputEnabledCom, AvmCode * aCode)
	{
		computeInputEnabledCom(anED, aRID, inputEnabledCom, aCode,
				& CommunicationDependency::isInputEnabledCom );
	}

	inline static void computeInputEnabledSave(
			const ExecutionData & anED, const RuntimeID & aRID,
			ListOfInstanceOfPort & inputEnabledSave, AvmCode * aCode )
	{
		computeInputEnabledCom(anED, aRID, inputEnabledSave, aCode,
				& CommunicationDependency::isInputEnabledSave );
	}



};

} /* namespace sep */

#endif /* COMMUNICATIONDEPENDENCY_H_ */
