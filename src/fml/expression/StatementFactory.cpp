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

#include "StatementFactory.h"

#include <fml/executable/AvmProgram.h>
#include <fml/executable/ExecutableForm.h>
#include <fml/executable/ExecutableLib.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/StatementTypeChecker.h>

#include <fml/infrastructure/Machine.h>

#include <fml/runtime/ExecutionData.h>


namespace sep
{


/**
 * COLLECT
 * [state]machine
 */
void StatementFactory::collectRunMachine(
		const BF & aStatement, ListOfInstanceOfMachine & listOfMachine)
{
	if( aStatement.invalid() )
	{
		return;
	}
	else switch( aStatement.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			const AvmCode & aCode = aStatement.to< AvmCode >();

			if( OperatorManager::isScheduledActivity( aCode.getOperator() ) )
			{
				if( aCode.first().is< InstanceOfMachine >() )
				{
					listOfMachine.add_unique(
							aCode.first().to_ptr< InstanceOfMachine >() );
				}
			}
			else if( OperatorManager::isSchedule( aCode.getOperator() )
					|| OperatorManager::isConditionnal( aCode.getOperator() ) )
			{
				for( const auto & itOperand : aCode.getOperands() )
				{
					collectRunMachine(itOperand, listOfMachine);
				}
			}

			break;
		}

		case FORM_INSTANCE_MACHINE_KIND:
		{
//			listOfMachine.add_unique( aStatement.to_ptr< InstanceOfMachine >() );

			break;
		}

		default:
		{
			break;
		}
	}
}


bool StatementFactory::hasActivityMachine(
		AVM_OPCODE opCode, const BF & aStatement)
{
	if( aStatement.invalid() )
	{
		return false;
	}
	else switch( aStatement.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			const AvmCode & aCode = aStatement.to< AvmCode >();

			if( aCode.isOpCode(opCode) && aCode.hasOperand() )
			{
				return( aCode.first().is< InstanceOfMachine >()
						|| aCode.first().is< Machine >() );
			}
			else if( OperatorManager::isSchedule( aCode.getOperator() )
					|| OperatorManager::isConditionnal( aCode.getOperator() ) )
			{
				for( const auto & itOperand : aCode.getOperands() )
				{
					if( hasActivityMachine(opCode, itOperand) )
					{
						return true;
					}
				}
			}

			return false;
		}

		case FORM_INSTANCE_MACHINE_KIND:
		{
//			listOfMachine.add_unique( aStatement.to_ptr< InstanceOfMachine >() );

			return false;
		}

		default:
		{
			return false;
		}
	}
}


void StatementFactory::collectActivityMachine(AVM_OPCODE opCode,
		const BF & aStatement, ListOfInstanceOfMachine & listOfMachine)
{
	if( aStatement.invalid() )
	{
		return;
	}
	else switch( aStatement.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			const AvmCode & aCode = aStatement.to< AvmCode >();

			if( aCode.isOpCode(opCode) && aCode.hasOperand() )
			{
				if( aCode.first().is< InstanceOfMachine >() )
				{
					listOfMachine.add_unique(
							aCode.first().to_ptr< InstanceOfMachine >() );
				}
			}
			else if( OperatorManager::isSchedule( aCode.getOperator() )
					|| OperatorManager::isConditionnal( aCode.getOperator() ) )
			{
				for( const auto & itOperand : aCode.getOperands() )
				{
					collectActivityMachine(opCode, itOperand, listOfMachine);
				}
			}

			break;
		}

		case FORM_INSTANCE_MACHINE_KIND:
		{
//			listOfMachine.add_unique( aStatement.to_ptr< InstanceOfMachine >() );

			break;
		}

		default:
		{
			break;
		}
	}
}


void StatementFactory::collectActivityMachine(AVM_OPCODE opCode,
		const BF & aStatement, BFCollection & listOfMachine)
{
	if( aStatement.invalid() )
	{
		return;
	}
	else switch( aStatement.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			const AvmCode & aCode = aStatement.to< AvmCode >();

			if( aCode.isOpCode(opCode) && aCode.hasOperand() )
			{
				if( aCode.first().is< InstanceOfMachine >() )
				{
					listOfMachine.add_unique( aCode.first() );
				}
			}
			else if( OperatorManager::isSchedule( aCode.getOperator() )
					|| OperatorManager::isConditionnal( aCode.getOperator() ) )
			{
				for( const auto & itOperand : aCode.getOperands() )
				{
					collectActivityMachine(opCode, itOperand, listOfMachine);
				}
			}

			break;
		}

		case FORM_INSTANCE_MACHINE_KIND:
		{
//			listOfMachine.add_unique( aStatement.to_ptr< InstanceOfMachine >() );

			break;
		}

		default:
		{
			break;
		}
	}
}



void StatementFactory::collectActivityMachine(
		AVM_OPCODE opCode1, AVM_OPCODE opCode2,
		const BF & aStatement, ListOfInstanceOfMachine & listOfMachine)
{
	if( aStatement.invalid() )
	{
		return;
	}
	else switch( aStatement.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			const AvmCode & aCode = aStatement.to< AvmCode >();

			if( aCode.isOpCode(opCode1) || aCode.isOpCode(opCode2) )
			{
				if(  aCode.hasOperand() && aCode.first().is< InstanceOfMachine >() )
				{
					listOfMachine.add_unique(
							aCode.first().to_ptr< InstanceOfMachine >() );
				}
			}
			else if( OperatorManager::isSchedule( aCode.getOperator() )
					|| OperatorManager::isConditionnal( aCode.getOperator() ) )
			{
				for( const auto & itOperand : aCode.getOperands() )
				{
					collectActivityMachine(
							opCode1, opCode2, itOperand, listOfMachine);
				}
			}

			break;
		}

		case FORM_INSTANCE_MACHINE_KIND:
		{
//			listOfMachine.add_unique( aStatement.to_ptr< InstanceOfMachine >() );

			break;
		}

		default:
		{
			break;
		}
	}
}


/**
 * COLLECT
 * Transition
 */
void StatementFactory::collectInvokeTransition(
		const ExecutableForm & anExecutableForm,
		const BF & aStatement, ListOfAvmTransition & listOfTransition)
{
	if( aStatement.invalid() )
	{
		return;
	}
	else switch( aStatement.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			const AvmCode & aCode = aStatement.to< AvmCode >();

			switch( aCode.getAvmOpCode() )
			{
				case AVM_OPCODE_INVOKE_TRANSITION:
				{
					if( aCode.hasOperand() &&  aCode.first().is< AvmTransition >() )
					{
						listOfTransition.add_unique(
								aCode.first().to_ptr< AvmTransition >() );
					}
					break;
				}

				case AVM_OPCODE_SCHEDULE_INVOKE:
				{
					if( aCode.noOperand() )
					{
						collectInvokeTransition(anExecutableForm,
								anExecutableForm.getOnSchedule(),
								listOfTransition );
					}
					break;
				}

				default:
				{
					for( const auto & itOperand : aCode.getOperands() )
					{
						collectInvokeTransition(
								anExecutableForm, itOperand, listOfTransition);
					}

					break;
				}
			}

			break;
		}


		case FORM_AVMTRANSITION_KIND:
		{
//			listOfTransition.add_unique( aStatement.to_ptr< AvmTransition >() );

			break;
		}


		default:
		{
			break;
		}
	}
}


/**
 * COLLECT
 * Communication Statement
 */
void StatementFactory::collectCommunication(
		const BF & aStatement, BFCollection & listOfComStatement)
{
	if( aStatement.is< AvmCode >() )
	{
		const AvmCode & aCode = aStatement.to< AvmCode >();

		if( StatementTypeChecker::isCommunication(aCode) )
		{
			listOfComStatement.append(aStatement);
		}
		else
		{
			for( const auto & itOperand : aCode.getOperands() )
			{
				collectCommunication(itOperand, listOfComStatement);
			}
		}
	}
}


/**
 * COLLECT
 * Guard & Communication Statement
 */
void StatementFactory::collectGuard(const BF & aStatement, BFCode & guard)
{
	if( aStatement.is< AvmCode >() )
	{
		const AvmCode & aCode = aStatement.to< AvmCode >();

		if( StatementTypeChecker::isGuard(aCode) )
		{
			guard = aStatement;
		}
		else
		{
			for( const auto & itOperand : aCode.getOperands() )
			{
				collectGuard(itOperand, guard);
			}
		}
	}
}

void StatementFactory::collectTimedGuard(const BF & aStatement, BFCode & timedGuard)
{
	if( aStatement.is< AvmCode >() )
	{
		const AvmCode & aCode = aStatement.to< AvmCode >();

		if( StatementTypeChecker::isTimedGuard(aCode) )
		{
			timedGuard = aStatement;
		}
		else
		{
			for( const auto & itOperand : aCode.getOperands() )
			{
				collectTimedGuard(itOperand, timedGuard);
			}
		}
	}
}

void StatementFactory::collectGuardCommunication(const BF & aStatement,
		BFCode & guard, BFCode & timedGuard, BFCode & comStatement)
{
	if( aStatement.is< AvmCode >() )
	{
		const AvmCode & aCode = aStatement.to< AvmCode >();

		if( StatementTypeChecker::isGuard(aCode) )
		{
			guard = aStatement;
		}
		else if( StatementTypeChecker::isTimedGuard(aCode) )
		{
			timedGuard = aStatement;
		}
		else if( StatementTypeChecker::isCommunication(aCode) )
		{
			comStatement = aStatement;
		}
		else
		{
			for( const auto & itOperand : aCode.getOperands() )
			{
				collectGuardCommunication(itOperand,
						guard, timedGuard, comStatement);
			}
		}
	}
}

/**
 * COLLECT
 * RID
 */
void StatementFactory::collectRID(const BF & aStatement,
		List< RuntimeID > & listOfRID)
{
	if( aStatement.invalid() )
	{
		return;
	}
	else switch( aStatement.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			for( const auto & itOperand :
				aStatement.to< AvmCode >().getOperands() )
			{
				collectRID(itOperand, listOfRID);
			}

			break;
		}

		case FORM_RUNTIME_ID_KIND:
		{
			listOfRID.add_unique( aStatement.bfRID() );

			break;
		}

		default:
		{
			break;
		}
	}
}


/**
 * CONTAINS
 * Activity on RID
 */
bool StatementFactory::containsOperationOnRID(const AvmCode & aCode,
		const AVM_OPCODE opActivity, const RuntimeID & aRID)
{
	if( aCode.hasOperand() )
	{
		if( aCode.isOpCode(opActivity) && ((aRID == aCode.first())
				/*|| aCode.contains(aRID)*/) )
		{
			return( true );
		}

		for( const auto & itOperand : aCode.getOperands() )
		{
			if( itOperand.is< AvmCode >()
				&& containsOperationOnRID(
						itOperand.to< AvmCode >(), opActivity, aRID) )
			{
				return( true );
			}
		}
	}

	return( false );
}


/**
 * get activity
 * ExecutableForm
 * or
 * RuntimeID
 */
const ExecutableForm * StatementFactory::getActivityTargetExecutable(
		const AvmProgram & anAvmProgram, const AvmCode & aCode)
{
//		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( aCode )	<< "AvmCode !!!"
//				<< SEND_EXIT;

	if( aCode.noOperand() )
	{
		return( anAvmProgram.getExecutable() );
	}
	else // if( aCode.singleton() )
	{
		if( aCode.first() == ExecutableLib::MACHINE_SELF )
		{
			return( anAvmProgram.getExecutable() );
		}
		else if( aCode.first().is< InstanceOfMachine >() )
		{
			return( aCode.first().to< InstanceOfMachine >()
					.getExecutable() );
		}
		else if( aCode.first().is< RuntimeID >() )
		{
			return( aCode.first().as_bf< RuntimeID >().getExecutable() );
		}
	}

	return( nullptr );
}


const RuntimeID & StatementFactory::getActivityTargetRID(
		const ExecutionData & anED,
		const RuntimeID & aRID, const AvmCode & aCode)
{
	if( aCode.noOperand() )
	{
		return( aRID );
	}
	else // if( aCode.singleton() )
	{
		if( aCode.first() == ExecutableLib::MACHINE_SELF )
		{
			return( aRID );
		}
		else if( aCode.first().is< RuntimeID >() )
		{
			return( aCode.first().as_bf< RuntimeID >() );
		}
		else if( aCode.first().is< InstanceOfMachine >() )
		{
			return( anED.getRuntimeID(
					aCode.first().to< InstanceOfMachine >()) );
		}
	}

	return( RuntimeID::nullref() );
}



}
