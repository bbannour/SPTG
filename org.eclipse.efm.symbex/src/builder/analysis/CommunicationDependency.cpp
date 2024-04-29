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

#include "CommunicationDependency.h"

#include <fml/expression/StatementFactory.h>

#include <fml/runtime/ExecutionData.h>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//// the communication information
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

BF CommunicationDependency::getCommunicationCodeOfTargetActivity(
		const AvmProgram & anAvmProgram,
		const BFCode & aCode, AVM_OPCODE activityOpCode,
		bool (*isCom)(const AvmCode & comCode), bool & hasMutableSchedule)
{
	const ExecutableForm * targetExec = StatementFactory::
				getActivityTargetExecutable(anAvmProgram, (* aCode));

	if( targetExec != nullptr )
	{
		return( getCommunicationCode((* targetExec),
				targetExec->getOnActivity(activityOpCode),
				isCom, hasMutableSchedule) );
	}

	return( BF::REF_NULL );
}

BF CommunicationDependency::getCommunicationCode(
		const AvmProgram & anAvmProgram, const BFCode & aCode,
		bool (*isCom)(const AvmCode & comCode), bool & hasMutableSchedule )
{
	if( isCom(* aCode) )
	{
		return( aCode );
	}
	else
	{
		AVM_OPCODE activityOpCode = ( anAvmProgram.isScopeTransition()
				? AVM_OPCODE_NULL : aCode.getAvmOpCode() );

		switch( activityOpCode )
		{
			case AVM_OPCODE_SCHEDULE_INVOKE:
			{
				const ExecutableForm * activityExec =
						StatementFactory::getActivityTargetExecutable(
								anAvmProgram, (* aCode));
				if( activityExec != nullptr )
				{
					if( activityExec->isMutableSchedule() )
					{
						hasMutableSchedule = true;
					}
					else
					{
						getCommunicationCode(*activityExec,
								activityExec->getOnSchedule(), isCom,
								hasMutableSchedule );
					}
				}

				return( BF::REF_NULL );
			}

			case AVM_OPCODE_INVOKE_TRANSITION:
			{
				const AvmProgram & argProgram =
						aCode->first().to< AvmProgram >();

				// Pour éviter les récursions infinis !!!
				if( isCom == (& CommunicationDependency::isCommunicationCode) )
				{
					return( argProgram.getCommunicationCode() );
				}
				else if( isCom ==
						(& CommunicationDependency::isInternalCommunicationCode) )
				{
					return( argProgram.getCommunicationCode() );
				}
				else if( isCom == (& CommunicationDependency::isEnvironmentCom) )
				{
					return( argProgram.getEnvironmentCom() );
				}
				else if( isCom ==
						(& CommunicationDependency::isEnvironmentInputCom) )
				{
					return( argProgram.getEnvironmentInputCom() );
				}
				else if( isCom ==
						(& CommunicationDependency::isEnvironmentOutputCom) )
				{
					return( argProgram.getEnvironmentOutputCom() );
				}

				else
				{
					return( getCommunicationCode(argProgram,
							argProgram.getCode(), isCom, hasMutableSchedule) );
				}

				return( BF::REF_NULL );
			}

			case AVM_OPCODE_IRUN:
			case AVM_OPCODE_RUN:
			case AVM_OPCODE_RTC:

			case AVM_OPCODE_IENABLE_INVOKE:
			case AVM_OPCODE_ENABLE_INVOKE:

			case AVM_OPCODE_IDISABLE_INVOKE:
			case AVM_OPCODE_DISABLE_INVOKE:

			case AVM_OPCODE_IABORT_INVOKE:
			case AVM_OPCODE_ABORT_INVOKE:
			{
				return( getCommunicationCodeOfTargetActivity(anAvmProgram,
						aCode, activityOpCode, isCom, hasMutableSchedule) );
			}


			default:
			{
				if( OperatorManager::isSchedule(aCode.getOperator()) )
				{
					AvmCode::OperandCollectionT listOfComArg;
					BF comArg;

					for( auto & itOperand : aCode->getOperands() )
					{
						if( itOperand.is< AvmCode >() )
						{
							comArg = getCommunicationCode(anAvmProgram,
								itOperand.bfCode(), isCom, hasMutableSchedule);

							if( comArg.valid() )
							{
								listOfComArg.append(comArg);
							}
						}
					}

					if( listOfComArg.populated() )
					{
						return( ExpressionConstructor::newCode(
								aCode.getOperator(), listOfComArg) );
					}
					else if( listOfComArg.nonempty() )
					{
						return( listOfComArg.pop_first() );
					}
				}

				return( BF::REF_NULL );
			}
		}
	}

	return( BF::REF_NULL );
}


/**
 * Collect information about
 * static input enabled communication
 */
void CommunicationDependency::computeInputEnabledComOfTargetActivity(
		const AvmProgram & anAvmProgram, ListOfInstanceOfPort & inputEnabledCom,
		const AvmCode & aCode, AVM_OPCODE activityOpCode,
		bool (*isCom)(const AvmCode & comCode), bool & hasMutableSchedule)
{
	const ExecutableForm * targetExec = StatementFactory::
			getActivityTargetExecutable(anAvmProgram, aCode);

	if( targetExec != nullptr )
	{
		computeInputEnabledCom((* targetExec), inputEnabledCom,
			targetExec->getOnActivity(activityOpCode),
			isCom, hasMutableSchedule );
	}

}

void CommunicationDependency::computeInputEnabledCom(
		const AvmProgram & anAvmProgram,
		ListOfInstanceOfPort & inputEnabledCom, const AvmCode & aCode,
		bool (*isCom)(const AvmCode & comCode), bool & hasMutableSchedule )
{
	if( isCom(aCode) )
	{
		if( aCode.first().is< InstanceOfPort >() )
		{
			inputEnabledCom.add_unique(
					aCode.first().to_ptr< InstanceOfPort >() );
		}
	}
	else
	{
		AVM_OPCODE activityOpCode = ( anAvmProgram.isScopeTransition()
				&& (not OperatorManager::isSchedule(aCode.getOperator())) )
						? AVM_OPCODE_NULL : aCode.getAvmOpCode();
		switch( activityOpCode )
		{
			case AVM_OPCODE_SCHEDULE_INVOKE:
			{
				const ExecutableForm * activityExec = StatementFactory::
						getActivityTargetExecutable(anAvmProgram, aCode);
				if( activityExec != nullptr )
				{
					if( activityExec->isMutableSchedule() )
					{
						hasMutableSchedule = true;
					}
					else
					{
						computeInputEnabledCom((* activityExec), inputEnabledCom,
								activityExec->getOnSchedule(), isCom,
								hasMutableSchedule );
					}
				}

				break;
			}

			case AVM_OPCODE_INVOKE_TRANSITION:
			{
				const AvmProgram & argProgram =
						aCode.first().to< AvmProgram >();

				// Pour éviter les récursions infinis !!!
				if( isCom == (& CommunicationDependency::isInputEnabledCom) )
				{
					inputEnabledCom.add_unique( argProgram.getInputEnabledCom() );
				}
				else if( isCom == (& CommunicationDependency::isInputEnabledSave) )
				{
					inputEnabledCom.add_unique( argProgram.getInputEnabledSave() );
				}

				else if( isCom == (& CommunicationDependency::isInputCom) )
				{
					inputEnabledCom.add_unique( argProgram.getInputCom() );
				}
				else if( isCom == (& CommunicationDependency::isOutputCom) )
				{
					inputEnabledCom.add_unique( argProgram.getOutputCom() );
				}

				else
				{
					computeInputEnabledCom(argProgram, inputEnabledCom,
							argProgram.getCode(), isCom, hasMutableSchedule );
				}

				break;
			}

			case AVM_OPCODE_IRUN:
			case AVM_OPCODE_RUN:
			case AVM_OPCODE_RTC:

			case AVM_OPCODE_IENABLE_INVOKE:
			case AVM_OPCODE_ENABLE_INVOKE:

			case AVM_OPCODE_IDISABLE_INVOKE:
			case AVM_OPCODE_DISABLE_INVOKE:

			case AVM_OPCODE_IABORT_INVOKE:
			case AVM_OPCODE_ABORT_INVOKE:
			{
				computeInputEnabledComOfTargetActivity(
						anAvmProgram, inputEnabledCom, aCode,
						activityOpCode, isCom, hasMutableSchedule );

				break;
			}


			// Justification of these switch statement
//			switch( ( anAvmProgram.isScopeTransition() &&
//					(not OperatorManager::isSchedule(aCode.getOperator())) ) ?
//							AVM_OPCODE_NUaCode.ode->getAvmOpCode() )

			case AVM_OPCODE_SEQUENCE:
			case AVM_OPCODE_ATOMIC_SEQUENCE:
			case AVM_OPCODE_SEQUENCE_SIDE:
			case AVM_OPCODE_PRIOR_GT:
			{
				ListOfInstanceOfPort localPorts;

				for( auto & itOperand : aCode.getOperands() )
				{
					if( itOperand.is< AvmCode >() )
					{
						computeInputEnabledCom( anAvmProgram, localPorts,
								itOperand.to< AvmCode >(), isCom,
								hasMutableSchedule );

						if( localPorts.nonempty() )
						{
							inputEnabledCom.add_unique(localPorts);

							break;
						}
					}
				}
				break;
			}

			case AVM_OPCODE_PRIOR_LT:
			{
				ListOfInstanceOfPort localPorts;

				AvmCode::OperandCollectionT::const_reverse_iterator itArg =
						aCode.getOperands().rbegin();
				AvmCode::OperandCollectionT::const_reverse_iterator itEndArg =
						aCode.getOperands().rend();
				for( ; itArg != itEndArg ; ++itArg )
				{
					if( (*itArg).is< AvmCode >() )
					{
						computeInputEnabledCom( anAvmProgram, localPorts,
								(*itArg).to< AvmCode >(), isCom,
								hasMutableSchedule );

						if( localPorts.nonempty() )
						{
							inputEnabledCom.add_unique(localPorts);

							break;
						}
					}
				}
				break;
			}

			default:
			{
				if( OperatorManager::isSchedule(aCode.getOperator()) )
				{
					for( const auto & itOperand : aCode.getOperands() )
					{
						if( itOperand.is< AvmCode >() )
						{
							computeInputEnabledCom(
									anAvmProgram, inputEnabledCom,
									itOperand.to< AvmCode >(), isCom,
									hasMutableSchedule );
						}
					}
				}

				break;
			}
		}
	}
}


/**
 * Collect information about
 * runtime input enabled communication
 */
void CommunicationDependency::computeInputEnabledCom(
		const ExecutionData & anED, const RuntimeID & aRID,
		ListOfInstanceOfPort & inputEnabledCom,
		const AvmCode & aCode, bool (*isCom)(const AvmCode & comCode) )
{
	if( isCom(aCode) )
	{
		if( aCode.first().is< InstanceOfPort >() )
		{
			inputEnabledCom.add_unique(
					aCode.first().to_ptr< InstanceOfPort >() );
		}
	}
	else
	{
		RuntimeID activityRID;

		switch( aCode.getAvmOpCode() )
		{
			case AVM_OPCODE_SCHEDULE_INVOKE:
			{
				if( (activityRID = StatementFactory::
						getActivityTargetRID(anED, aRID, aCode)).valid() )
				{
					if( activityRID.refExecutable().isMutableSchedule() )
					{
						computeInputEnabledCom(anED, activityRID, inputEnabledCom,
							anED.getRuntimeFormOnSchedule(activityRID), isCom);
					}
					else
					{
						computeInputEnabledCom(anED, activityRID, inputEnabledCom,
								activityRID.refExecutable().getOnSchedule(),
								isCom );
					}
				}

				break;
			}

			case AVM_OPCODE_INVOKE_TRANSITION:
			{
				const AvmProgram & argProgram =
						aCode.first().to< AvmProgram >();

				// Pour éviter les récursions infinis !!!
				if( isCom == (& CommunicationDependency::isInputEnabledCom) )
				{
					inputEnabledCom.add_unique( argProgram.getInputEnabledCom() );
				}
				else if( isCom == (& CommunicationDependency::isInputEnabledSave) )
				{
					inputEnabledCom.add_unique( argProgram.getInputEnabledSave() );
				}

				else if( isCom == (& CommunicationDependency::isInputCom) )
				{
					inputEnabledCom.add_unique( argProgram.getInputCom() );
				}
				else if( isCom == (& CommunicationDependency::isOutputCom) )
				{
					inputEnabledCom.add_unique( argProgram.getOutputCom() );
				}

				else
				{
					computeInputEnabledCom(anED, activityRID,
							inputEnabledCom, argProgram.getCode(), isCom);
				}

				break;
			}

			case AVM_OPCODE_IRUN:
			{
				if( (activityRID = StatementFactory::
						getActivityTargetRID(anED, aRID, aCode)).valid() )
				{
					computeInputEnabledCom(anED, activityRID, inputEnabledCom,
							activityRID.refExecutable().getOnIRun(), isCom );
				}

				break;
			}
			case AVM_OPCODE_RUN:
			{
				if( (activityRID = StatementFactory::
						getActivityTargetRID(anED, aRID, aCode)).valid() )
				{
					computeInputEnabledCom(anED, activityRID, inputEnabledCom,
							activityRID.refExecutable().getOnRun(), isCom );
				}

				break;
			}
			case AVM_OPCODE_RTC:
			{
				if( (activityRID = StatementFactory::
						getActivityTargetRID(anED, aRID, aCode)) != nullptr )
				{
					computeInputEnabledCom(anED, activityRID, inputEnabledCom,
							activityRID.refExecutable().getOnRtc(), isCom );
				}

				break;
			}

			case AVM_OPCODE_IENABLE_INVOKE:
			{
				if( (activityRID = StatementFactory::
						getActivityTargetRID(anED, aRID, aCode)).valid() )
				{
					computeInputEnabledCom(anED, activityRID, inputEnabledCom,
							activityRID.refExecutable().getOnIEnable(),
							isCom );
				}

				break;
			}
			case AVM_OPCODE_ENABLE_INVOKE:
			{
				if( (activityRID = StatementFactory::
						getActivityTargetRID(anED, aRID, aCode)).valid() )
				{
					computeInputEnabledCom(anED, activityRID, inputEnabledCom,
							activityRID.refExecutable().getOnEnable(),
							isCom );
				}

				break;
			}

			case AVM_OPCODE_IDISABLE_INVOKE:
			{
				if( (activityRID = StatementFactory::
						getActivityTargetRID(anED, aRID, aCode)).valid() )
				{
					computeInputEnabledCom(anED, activityRID, inputEnabledCom,
							activityRID.refExecutable().getOnIDisable(),
							isCom );
				}

				break;
			}
			case AVM_OPCODE_DISABLE_INVOKE:
			{
				if( (activityRID = StatementFactory::
						getActivityTargetRID(anED, aRID, aCode)).valid() )
				{
					computeInputEnabledCom(anED, activityRID, inputEnabledCom,
							activityRID.refExecutable().getOnDisable(),
							isCom );
				}

				break;
			}

			case AVM_OPCODE_IABORT_INVOKE:
			{
				if( (activityRID = StatementFactory::
						getActivityTargetRID(anED, aRID, aCode)).valid() )
				{
					computeInputEnabledCom(anED, activityRID, inputEnabledCom,
							activityRID.refExecutable().getOnIAbort(),
							isCom );
				}

				break;
			}
			case AVM_OPCODE_ABORT_INVOKE:
			{
				if( (activityRID = StatementFactory::
						getActivityTargetRID(anED, aRID, aCode)).valid() )
				{
					computeInputEnabledCom(anED, activityRID, inputEnabledCom,
							activityRID.refExecutable().getOnAbort(), isCom );
				}

				break;
			}


			case AVM_OPCODE_SEQUENCE:
			case AVM_OPCODE_ATOMIC_SEQUENCE:
			case AVM_OPCODE_SEQUENCE_SIDE:
			case AVM_OPCODE_PRIOR_GT:
			{
				ListOfInstanceOfPort localPorts;

				for( auto & itOperand : aCode.getOperands() )
				{
					if( itOperand.is< AvmCode >() )
					{
						computeInputEnabledCom(anED, aRID, localPorts,
								itOperand.to< AvmCode >(), isCom );

						if( localPorts.nonempty() )
						{
							inputEnabledCom.add_unique(localPorts);

							break;
						}
					}
				}
				break;
			}

			case AVM_OPCODE_PRIOR_LT:
			{
				ListOfInstanceOfPort localPorts;

				AvmCode::OperandCollectionT::const_reverse_iterator itArg =
						aCode.getOperands().rbegin();
				AvmCode::OperandCollectionT::const_reverse_iterator itEndArg =
						aCode.getOperands().rend();
				for( ; itArg != itEndArg ; ++itArg )
				{
					if( (*itArg).is< AvmCode >() )
					{
						computeInputEnabledCom(anED, aRID, localPorts,
								(*itArg).to< AvmCode >(), isCom );

						if( localPorts.nonempty() )
						{
							inputEnabledCom.add_unique(localPorts);

							break;
						}
					}
				}
				break;
			}

			default:
			{
				if( OperatorManager::isSchedule(aCode.getOperator()) )
				{
					for( auto & itOperand : aCode.getOperands() )
					{
						if( itOperand.is< AvmCode >() )
						{
							computeInputEnabledCom(
									anED, aRID, inputEnabledCom,
									itOperand.to< AvmCode >(), isCom );
						}
					}
				}

				break;
			}
		}
	}
}


} /* namespace sep */
