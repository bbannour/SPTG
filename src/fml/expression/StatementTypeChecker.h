/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 25 sept. 2009
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef STATEMENTTYPECHECKER_H_
#define STATEMENTTYPECHECKER_H_

#include <common/BF.h>

#include <fml/expression/AvmCode.h>

#include <fml/operator/OperatorManager.h>


namespace sep
{


class Element;


class StatementTypeChecker
{

public:

	////////////////////////////////////////////////////////////////////////////
	// KIND CHECKER
	////////////////////////////////////////////////////////////////////////////

	inline static bool isStructured(const BF & aCode)
	{
		return( aCode.is< AvmCode >()
				&& isStructured(aCode.to< AvmCode >()) );
	}

	inline static bool isStructured(const AvmCode & aCode)
	{
		return( OperatorManager::isSchedule( aCode.getOperator() ) ||
				OperatorManager::isConditionnal( aCode.getOperator() ) );
	}


	inline static bool isAssign(const BF & aCode)
	{
		return( aCode.is< AvmCode >()
				&& isAssign(aCode.to< AvmCode >()) );
	}

	inline static bool isAssign(const AvmCode & aCode)
	{
		return( OperatorManager::isAssign( aCode.getOperator() ) );
	}


	inline static bool isGuard(const BF & aCode)
	{
		return( aCode.is< AvmCode >()
				&& isGuard(aCode.to< AvmCode >()) );
	}

	inline static bool isGuard(const AvmCode & aCode)
	{
		return( OperatorManager::isGuard( aCode.getOperator() ) );
	}

	inline static bool isTimedGuard(const BF & aCode)
	{
		return( aCode.is< AvmCode >()
				&& isTimedGuard(aCode.to< AvmCode >()) );
	}

	inline static bool isTimedGuard(const AvmCode & aCode)
	{
		return( OperatorManager::isTimedGuard( aCode.getOperator() ) );
	}


	inline static bool isSequence(const BF & aCode)
	{
		return( aCode.is< AvmCode >()
				&& isSequence(aCode.to< AvmCode >()) );
	}

	inline static bool isSequence(const AvmCode & aCode)
	{
		return( OperatorManager::isSequence( aCode.getOperator() ) );
	}

	inline static bool isEmptySequence(const AvmCode & aCode)
	{
		return( aCode.noOperand()
				&& OperatorManager::isSequence( aCode.getOperator() ) );
	}


	inline static bool isSchedule(const BF & aCode)
	{
		return( aCode.is< AvmCode >()
				&& isSchedule(aCode.to< AvmCode >()) );
	}

	inline static bool isSchedule(const AvmCode & aCode)
	{
		return( OperatorManager::isSchedule( aCode.getOperator() ) );
	}


	inline static bool isMachine(const BF & aCode)
	{
		return( aCode.is< AvmCode >()
				&& isMachine(aCode.to< AvmCode >()) );
	}

	inline static bool isMachine(const AvmCode & aCode)
	{
		return( OperatorManager::isMachine( aCode.getOperator() ) );
	}


	inline static bool isActivity(const BF & aCode)
	{
		return( aCode.is< AvmCode >()
				&& isActivity(aCode.to< AvmCode >()) );
	}

	inline static bool isActivity(const AvmCode & aCode)
	{
		return( OperatorManager::isActivity( aCode.getOperator() ) );
	}


	inline static bool isInvokeNew(const BF & aCode)
	{
		return( aCode.is< AvmCode >()
				&& isInvokeNew(aCode.to< AvmCode >()) );
	}

	inline static bool isInvokeNew(const AvmCode & aCode)
	{
		return( aCode.getOperator() == OperatorManager::OPERATOR_INVOKE_NEW );
	}


	inline static bool isCommunication(const BF & aCode)
	{
		return( aCode.is< AvmCode >()
				&& isCommunication(aCode.to< AvmCode >()) );
	}

	inline static bool isCommunication(const AvmCode & aCode)
	{
		return( OperatorManager::isCommunication( aCode.getOperator() ) );
	}


	inline static bool isInput(const BF & aCode)
	{
		return( aCode.is< AvmCode >()
				&& isInput(aCode.to< AvmCode >()) );
	}

	inline static bool isInput(const AvmCode & aCode)
	{
		return( OperatorManager::isInput( aCode.getOperator() ) );
	}


	inline static bool isOutput(const BF & aCode)
	{
		return( aCode.is< AvmCode >()
				&& isOutput(aCode.to< AvmCode >()) );
	}

	inline static bool isOutput(const AvmCode & aCode)
	{
		return( OperatorManager::isOutput( aCode.getOperator() ) );
	}


	inline static bool isConditionnal(const BF & aCode)
	{
		return( aCode.is< AvmCode >()
				&& isConditionnal(aCode.to< AvmCode >()) );
	}

	inline static bool isConditionnal(const AvmCode & aCode)
	{
		return( OperatorManager::isConditionnal( aCode.getOperator() ) );
	}


	inline static bool isStatement(const BF & aCode)
	{
		return( aCode.is< AvmCode >()
				&& isStatement(aCode.to< AvmCode >()) );
	}

	inline static bool isStatement(const AvmCode & aCode)
	{
		return( OperatorManager::isStatement( aCode.getOperator() ) );
	}


	inline static bool isAtomicStatement(const BF & aCode)
	{
		return( aCode.is< AvmCode >()
				&& isAtomicStatement(aCode.to< AvmCode >()) );
	}

	inline static bool isAtomicStatement(const AvmCode & aCode)
	{
		return( OperatorManager::isAtomicStatement( aCode.getOperator() ) );
	}


	inline static bool isAtomicSequence(const BF & aCode)
	{
		return( aCode.is< AvmCode >()
				&& isAtomicSequence(aCode.to< AvmCode >()) );
	}

	inline static bool isAtomicSequence(const AvmCode & aCode)
	{
		return( aCode.isOpCode( AVM_OPCODE_ATOMIC_SEQUENCE ) );
	}


	inline static bool isStrongAtomicSequence(const BF & aCode)
	{
		return( aCode.is< AvmCode >()
				&& isStrongAtomicSequence(aCode.to< AvmCode >()) );
	}

	inline static bool isStrongAtomicSequence(const AvmCode & aCode)
	{
		return( aCode.isOpCode( AVM_OPCODE_ATOMIC_SEQUENCE )
				&& ( aCode.noOperand()
					|| isAtomicStatement(aCode.last()) ) );
	}


	inline static bool isComment(const BF & aCode)
	{
		return( aCode.is< AvmCode >()
				&& isComment(aCode.to< AvmCode >()) );
	}

	inline static bool isComment(const AvmCode & aCode)
	{
		return( aCode.isOpCode( AVM_OPCODE_COMMENT ) );
	}


	////////////////////////////////////////////////////////////////////////////
	// EMPTYNESS CHECKER
	////////////////////////////////////////////////////////////////////////////

	inline static bool isEmptySchedule(const AvmCode & aCode)
	{
		return( aCode.noOperand()
				&& OperatorManager::isSchedule( aCode.getOperator() ) );
	}

	////////////////////////////////////////////////////////////////////////////
	// DO SOMETHING CHECKER
	////////////////////////////////////////////////////////////////////////////

	inline static bool doSomething(const AvmCode & aCode)
	{
		return( aCode.hasOperand() || (not isSchedule(aCode)) );
	}




};


}

#endif /* STATEMENTTYPECHECKER_H_ */
