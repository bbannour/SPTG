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
		return( aCode.is< AvmCode >() &&
				isStructured(aCode.to_ptr< AvmCode >()) );
	}

	inline static bool isStructured(AvmCode * aCode)
	{
		return( OperatorManager::isSchedule( aCode->getOperator() ) ||
				OperatorManager::isConditionnal( aCode->getOperator() ) );
	}


	inline static bool isAssign(const BF & aCode)
	{
		return( aCode.is< AvmCode >() &&
				isAssign(aCode.to_ptr< AvmCode >()) );
	}

	inline static bool isAssign(AvmCode * aCode)
	{
		return( OperatorManager::isAssign( aCode->getOperator() ) );
	}


	inline static bool isSequence(const BF & aCode)
	{
		return( aCode.is< AvmCode >() &&
				isSequence(aCode.to_ptr< AvmCode >()) );
	}

	inline static bool isSequence(AvmCode * aCode)
	{
		return( OperatorManager::isSequence( aCode->getOperator() ) );
	}


	inline static bool isSchedule(const BF & aCode)
	{
		return( aCode.is< AvmCode >() &&
				isSchedule(aCode.to_ptr< AvmCode >()) );
	}

	inline static bool isSchedule(AvmCode * aCode)
	{
		return( OperatorManager::isSchedule( aCode->getOperator() ) );
	}


	inline static bool isMachine(const BF & aCode)
	{
		return( aCode.is< AvmCode >() &&
				isMachine(aCode.to_ptr< AvmCode >()) );
	}

	inline static bool isMachine(AvmCode * aCode)
	{
		return( OperatorManager::isMachine( aCode->getOperator() ) );
	}


	inline static bool isActivity(const BF & aCode)
	{
		return( aCode.is< AvmCode >() &&
				isActivity(aCode.to_ptr< AvmCode >()) );
	}

	inline static bool isActivity(AvmCode * aCode)
	{
		return( OperatorManager::isActivity( aCode->getOperator() ) );
	}


	inline static bool isInvokeNew(const BF & aCode)
	{
		return( aCode.is< AvmCode >() &&
				isInvokeNew(aCode.to_ptr< AvmCode >()) );
	}

	inline static bool isInvokeNew(AvmCode * aCode)
	{
		return( aCode->getOperator() == OperatorManager::OPERATOR_INVOKE_NEW );
	}


	inline static bool isCommunication(const BF & aCode)
	{
		return( aCode.is< AvmCode >() &&
				isCommunication(aCode.to_ptr< AvmCode >()) );
	}

	inline static bool isCommunication(AvmCode * aCode)
	{
		return( OperatorManager::isCommunication( aCode->getOperator() ) );
	}


	inline static bool isConditionnal(const BF & aCode)
	{
		return( aCode.is< AvmCode >() &&
				isConditionnal(aCode.to_ptr< AvmCode >()) );
	}

	inline static bool isConditionnal(AvmCode * aCode)
	{
		return( OperatorManager::isConditionnal( aCode->getOperator() ) );
	}


	inline static bool isStatement(const BF & aCode)
	{
		return( aCode.is< AvmCode >() &&
				isStatement(aCode.to_ptr< AvmCode >()) );
	}

	inline static bool isStatement(AvmCode * aCode)
	{
		return( OperatorManager::isStatement( aCode->getOperator() ) );
	}


	inline static bool isAtomicStatement(const BF & aCode)
	{
		return( aCode.is< AvmCode >() &&
				isAtomicStatement(aCode.to_ptr< AvmCode >()) );
	}

	inline static bool isAtomicStatement(AvmCode * aCode)
	{
		return( OperatorManager::isAtomicStatement( aCode->getOperator() ) );
	}


	inline static bool isAtomicSequence(const BF & aCode)
	{
		return( aCode.is< AvmCode >() &&
				isAtomicSequence(aCode.to_ptr< AvmCode >()) );
	}

	inline static bool isAtomicSequence(AvmCode * aCode)
	{
		return( aCode->isOpCode( AVM_OPCODE_ATOMIC_SEQUENCE ) );
	}


	inline static bool isStrongAtomicSequence(const BF & aCode)
	{
		return( aCode.is< AvmCode >() &&
				isStrongAtomicSequence(aCode.to_ptr< AvmCode >()) );
	}

	inline static bool isStrongAtomicSequence(AvmCode * aCode)
	{
		return( aCode->isOpCode( AVM_OPCODE_ATOMIC_SEQUENCE ) &&
				(aCode->empty() || isAtomicStatement(aCode->last()))  );
	}


	inline static bool isComment(const BF & aCode)
	{
		return( aCode.is< AvmCode >() &&
				isComment(aCode.to_ptr< AvmCode >()) );
	}

	inline static bool isComment(AvmCode * aCode)
	{
		return( aCode->isOpCode( AVM_OPCODE_COMMENT ) );
	}


	////////////////////////////////////////////////////////////////////////////
	// EMPTYNESS CHECKER
	////////////////////////////////////////////////////////////////////////////

	inline static bool isEmptySchedule(AvmCode * aCode)
	{
		return( aCode->empty() &&
				OperatorManager::isSchedule( aCode->getOperator() ) );
	}

	////////////////////////////////////////////////////////////////////////////
	// DO SOMETHING CHECKER
	////////////////////////////////////////////////////////////////////////////

	inline static bool doSomething(AvmCode * aCode)
	{
		return( aCode->nonempty() || (! isSchedule(aCode)) );
	}




};


}

#endif /* STATEMENTTYPECHECKER_H_ */
