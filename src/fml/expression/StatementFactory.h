/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 23 sept. 2009
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef STATEMENTFACTORY_H_
#define STATEMENTFACTORY_H_

#include <collection/Typedef.h>
#include <collection/BFContainer.h>

#include <fml/executable/AvmTransition.h>
#include <fml/executable/ExecutableLib.h>
#include <fml/executable/InstanceOfMachine.h>

#include <fml/operator/OperatorLib.h>
#include <fml/operator/OperatorLib.h>

#include <fml/runtime/RuntimeID.h>


namespace sep
{

class AvmCode;
class AvmProgram;
class ExecutableForm;
class ExecutionData;
class Operator;


class StatementFactory
{

public:

	/**
	 * COLLECT
	 * [state]machine
	 */
	static void collectRunMachine(
			const BF & aStatement, ListOfInstanceOfMachine & listOfMachine);

	static bool hasActivityMachine(AVM_OPCODE opCode, const BF & aStatement);

	static void collectActivityMachine(AVM_OPCODE opCode,
			const BF & aStatement, ListOfInstanceOfMachine & listOfMachine);

	static void collectActivityMachine(AVM_OPCODE opCode,
			const BF & aStatement, BFCollection & listOfMachine);

	static void collectActivityMachine(AVM_OPCODE opCode1, AVM_OPCODE opCode2,
			const BF & aStatement, ListOfInstanceOfMachine & listOfMachine);


	/**
	 * COLLECT
	 * Transition
	 */
	static void collectInvokeTransition(const ExecutableForm & anExecutableForm,
			const BF & aStatement, ListOfAvmTransition & listOfTransition);

	/**
	 * COLLECT
	 * Communication Statement
	 */
	static void collectCommunication(
			const BF & aStatement, BFCollection & listOfComStatement);

	/**
	 * COLLECT
	 * Guard & Communication Statement
	 */
	static void collectGuard(const BF & aStatement, BFCode & guard);

	static void collectTimedGuard(const BF & aStatement, BFCode & timedGuard);

	static void collectGuardCommunication(const BF & aStatement,
			BFCode & guard, BFCode & timedGuard, BFCode & comStatement);

	/**
	 * COLLECT
	 * RID
	 */
	static void collectRID(const BF & aStatement,
			List< RuntimeID > & listOfRID);

	/**
	 * CONTAINS
	 * Activity on RID
	 */
	static bool containsOperationOnRID(const AvmCode & aCode,
			const AVM_OPCODE opActivity, const RuntimeID & aRID);

	/**
	 * is activity statement is
	 * void
	 * or
	 * singleton const::machine#self
	 */
	inline static bool isActivityOnSelf(const AvmCode & aCode)
	{
//		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( aCode ) << "AvmCode" ); !!!"
//				<< SEND_EXIT;

		return( aCode.noOperand()
				|| ( aCode.hasOneOperand()
					&& (aCode.first() == ExecutableLib::MACHINE_SELF) ) );
	}

	/**
	 * get activity
	 * ExecutableForm
	 * or
	 * RuntimeID
	 */
	static const ExecutableForm * getActivityTargetExecutable(
			const AvmProgram & anAvmProgram, const AvmCode & aCode);


	static const RuntimeID & getActivityTargetRID(
			const ExecutionData & anED,
			const RuntimeID & aRID, const AvmCode & aCode);


};


}

#endif /* STATEMENTFACTORY_H_ */
