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

BF CommunicationDependency::getCommunicationCode(
		AvmProgram * anAvmProgram, const BFCode & aCode,
		bool (*isCom)(AvmCode * comCode), bool & hasMutableSchedule )
{
	if( aCode.invalid() )
	{
		//!! NOTHING
		return( BF::REF_NULL );
	}
	else if( isCom(aCode) )
	{
		return( aCode );
	}
	else
	{
		ExecutableForm * activityExec = NULL;

		switch( anAvmProgram->isScopeTransition() ? //is< AvmTransition >()
				AVM_OPCODE_NULL : aCode->getAvmOpCode() )
		{
			case AVM_OPCODE_SCHEDULE_INVOKE:
			{
				if( (activityExec = StatementFactory::
						getActivityTargetExecutable(anAvmProgram, aCode))
						!= NULL )
				{
					if( activityExec->isMutableSchedule() )
					{
						hasMutableSchedule = true;
					}
					else
					{
						getCommunicationCode(activityExec,
								activityExec->getOnSchedule(), isCom,
								hasMutableSchedule );
					}
				}

				return( BF::REF_NULL );
			}

			case AVM_OPCODE_INVOKE_TRANSITION:
			{
				// Pour éviter les récursions infinis !!!
				if( isCom == (& CommunicationDependency::isCommunicationCode) )
				{
					return( aCode->first().to_ptr< AvmProgram >()
							->getCommunicationCode() );
				}
				else if( isCom ==
						(& CommunicationDependency::isInternalCommunicationCode) )
				{
					return( aCode->first().to_ptr< AvmProgram >()
							->getCommunicationCode() );
				}
				else if( isCom == (& CommunicationDependency::isEnvironmentCom) )
				{
					return( aCode->first().to_ptr< AvmProgram >()
							->getEnvironmentCom() );
				}
				else if( isCom ==
						(& CommunicationDependency::isEnvironmentInputCom) )
				{
					return( aCode->first().to_ptr< AvmProgram >()
							->getEnvironmentInputCom() );
				}
				else if( isCom ==
						(& CommunicationDependency::isEnvironmentOutputCom) )
				{
					return( aCode->first().to_ptr< AvmProgram >()
							->getEnvironmentOutputCom() );
				}

				else
				{
					return( getCommunicationCode(
							aCode->first().to_ptr< AvmProgram >(),
							aCode->first().to_ptr< AvmProgram >()->getCode(),
							isCom, hasMutableSchedule) );
				}

				return( BF::REF_NULL );
			}

			case AVM_OPCODE_IRUN:
			{
				if( (activityExec = StatementFactory::
						getActivityTargetExecutable(anAvmProgram, aCode))
						!= NULL )
				{
					return( getCommunicationCode(activityExec,
							activityExec->getOnIRun(), isCom,
							hasMutableSchedule) );
				}

				return( BF::REF_NULL );
			}
			case AVM_OPCODE_RUN:
			{
				if( (activityExec = StatementFactory::
						getActivityTargetExecutable(anAvmProgram, aCode))
						!= NULL )
				{
					return( getCommunicationCode(activityExec,
							activityExec->getOnRun(), isCom,
							hasMutableSchedule) );
				}

				return( BF::REF_NULL );
			}
			case AVM_OPCODE_RTC:
			{
				if( (activityExec = StatementFactory::
						getActivityTargetExecutable(anAvmProgram, aCode))
						!= NULL )
				{
					return( getCommunicationCode(activityExec,
							activityExec->getOnRtc(), isCom,
							hasMutableSchedule) );
				}

				return( BF::REF_NULL );
			}

			case AVM_OPCODE_IENABLE_INVOKE:
			{
				if( (activityExec = StatementFactory::
						getActivityTargetExecutable(anAvmProgram, aCode))
						!= NULL )
				{
					return( getCommunicationCode(activityExec,
							activityExec->getOnIEnable(), isCom,
							hasMutableSchedule) );
				}

				return( BF::REF_NULL );
			}
			case AVM_OPCODE_ENABLE_INVOKE:
			{
				if( (activityExec = StatementFactory::
						getActivityTargetExecutable(anAvmProgram, aCode))
						!= NULL )
				{
					return( getCommunicationCode(activityExec,
							activityExec->getOnEnable(), isCom,
							hasMutableSchedule) );
				}

				return( BF::REF_NULL );
			}

			case AVM_OPCODE_IDISABLE_INVOKE:
			{
				if( (activityExec = StatementFactory::
						getActivityTargetExecutable(anAvmProgram, aCode))
						!= NULL )
				{
					return( getCommunicationCode(activityExec,
							activityExec->getOnIDisable(), isCom,
							hasMutableSchedule) );
				}

				return( BF::REF_NULL );
			}
			case AVM_OPCODE_DISABLE_INVOKE:
			{
				if( (activityExec = StatementFactory::
						getActivityTargetExecutable(anAvmProgram, aCode))
						!= NULL )
				{
					return( getCommunicationCode(activityExec,
							activityExec->getOnDisable(), isCom,
							hasMutableSchedule) );
				}

				return( BF::REF_NULL );
			}

			case AVM_OPCODE_IABORT_INVOKE:
			{
				if( (activityExec = StatementFactory::
						getActivityTargetExecutable(anAvmProgram, aCode))
						!= NULL )
				{
					return( getCommunicationCode(activityExec,
							activityExec->getOnIAbort(), isCom,
							hasMutableSchedule) );
				}

				return( BF::REF_NULL );
			}
			case AVM_OPCODE_ABORT_INVOKE:
			{
				if( (activityExec = StatementFactory::
						getActivityTargetExecutable(anAvmProgram, aCode))
						!= NULL )
				{
					return( getCommunicationCode(activityExec,
							activityExec->getOnAbort(), isCom,
							hasMutableSchedule) );
				}

				return( BF::REF_NULL );
			}


			default:
			{
				if( OperatorManager::isSchedule(aCode->getOperator()) )
				{
					AvmCode::this_container_type listOfComArg;
					BF comArg;

					AvmCode::iterator itArg = aCode->begin();
					AvmCode::iterator itEndArg = aCode->end();
					for( ; itArg != itEndArg ; ++itArg )
					{
						if( (*itArg).is< AvmCode >() )
						{
							comArg = getCommunicationCode(anAvmProgram,
								(*itArg).bfCode(), isCom, hasMutableSchedule);

							if( comArg.valid() )
							{
								listOfComArg.append(comArg);
							}
						}
					}

					if( listOfComArg.populated() )
					{
						return( ExpressionConstructor::newCode(
								aCode->getOperator(), listOfComArg) );
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
void CommunicationDependency::computeInputEnabledCom(AvmProgram * anAvmProgram,
		ListOfInstanceOfPort & inputEnabledCom, AvmCode * aCode,
		bool (*isCom)(AvmCode * comCode), bool & hasMutableSchedule )
{
	if( aCode == NULL )
	{
		//!! NOTHING
		return;
	}
	else if( isCom(aCode) )
	{
		if( aCode->first().is< InstanceOfPort >() )
		{
			inputEnabledCom.add_union( aCode->first().to_ptr< InstanceOfPort >() );
		}
	}
	else
	{
		ExecutableForm * activityExec = NULL;

		switch( ( anAvmProgram->isScopeTransition() && //is< AvmTransition >()
				(not OperatorManager::isSchedule(aCode->getOperator())) ) ?
						AVM_OPCODE_NULL : aCode->getAvmOpCode() )
		{
			case AVM_OPCODE_SCHEDULE_INVOKE:
			{
				if( (activityExec = StatementFactory::
						getActivityTargetExecutable(anAvmProgram, aCode))
						!= NULL )
				{
					if( activityExec->isMutableSchedule() )
					{
						hasMutableSchedule = true;
					}
					else
					{
						computeInputEnabledCom(activityExec, inputEnabledCom,
								activityExec->getOnSchedule(), isCom,
								hasMutableSchedule );
					}
				}

				break;
			}

			case AVM_OPCODE_INVOKE_TRANSITION:
			{
				// Pour éviter les récursions infinis !!!
				if( isCom == (& CommunicationDependency::isInputEnabledCom) )
				{
					inputEnabledCom.add_union( aCode->first().
							to_ptr< AvmProgram >()->getInputEnabledCom() );
				}
				else if( isCom == (& CommunicationDependency::isInputEnabledSave) )
				{
					inputEnabledCom.add_union( aCode->first().
							to_ptr< AvmProgram >()->getInputEnabledSave() );
				}

				else if( isCom == (& CommunicationDependency::isInputCom) )
				{
					inputEnabledCom.add_union( aCode->first().
							to_ptr< AvmProgram >()->getInputCom() );
				}
				else if( isCom == (& CommunicationDependency::isOutputCom) )
				{
					inputEnabledCom.add_union( aCode->first().
							to_ptr< AvmProgram >()->getOutputCom() );
				}

				else
				{
					computeInputEnabledCom(
							aCode->first().to_ptr< AvmProgram >(),
							inputEnabledCom,
							aCode->first().to_ptr< AvmProgram >()->getCode(),
							isCom, hasMutableSchedule );
				}

				break;
			}

			case AVM_OPCODE_IRUN:
			{
				if( (activityExec = StatementFactory::
						getActivityTargetExecutable(anAvmProgram, aCode))
						!= NULL )
				{
					computeInputEnabledCom(activityExec, inputEnabledCom,
							activityExec->getOnIRun(), isCom,
							hasMutableSchedule );
				}

				break;
			}
			case AVM_OPCODE_RUN:
			{
				if( (activityExec = StatementFactory::
						getActivityTargetExecutable(anAvmProgram, aCode))
						!= NULL )
				{
					computeInputEnabledCom(activityExec, inputEnabledCom,
							activityExec->getOnRun(), isCom,
							hasMutableSchedule );
				}

				break;
			}
			case AVM_OPCODE_RTC:
			{
				if( (activityExec = StatementFactory::
						getActivityTargetExecutable(anAvmProgram, aCode)) != NULL )
				{
					computeInputEnabledCom(activityExec, inputEnabledCom,
							activityExec->getOnRtc(), isCom,
							hasMutableSchedule );
				}

				break;
			}

			case AVM_OPCODE_IENABLE_INVOKE:
			{
				if( (activityExec = StatementFactory::
						getActivityTargetExecutable(anAvmProgram, aCode))
						!= NULL )
				{
					computeInputEnabledCom(activityExec, inputEnabledCom,
							activityExec->getOnIEnable(), isCom,
							hasMutableSchedule );
				}

				break;
			}
			case AVM_OPCODE_ENABLE_INVOKE:
			{
				if( (activityExec = StatementFactory::
						getActivityTargetExecutable(anAvmProgram, aCode))
						!= NULL )
				{
					computeInputEnabledCom(activityExec, inputEnabledCom,
							activityExec->getOnEnable(), isCom,
							hasMutableSchedule );
				}

				break;
			}

			case AVM_OPCODE_IDISABLE_INVOKE:
			{
				if( (activityExec = StatementFactory::
						getActivityTargetExecutable(anAvmProgram, aCode))
						!= NULL )
				{
					computeInputEnabledCom(activityExec, inputEnabledCom,
							activityExec->getOnIDisable(), isCom,
							hasMutableSchedule );
				}

				break;
			}
			case AVM_OPCODE_DISABLE_INVOKE:
			{
				if( (activityExec = StatementFactory::
						getActivityTargetExecutable(anAvmProgram, aCode))
						!= NULL )
				{
					computeInputEnabledCom(activityExec, inputEnabledCom,
							activityExec->getOnDisable(), isCom,
							hasMutableSchedule );
				}

				break;
			}

			case AVM_OPCODE_IABORT_INVOKE:
			{
				if( (activityExec = StatementFactory::
						getActivityTargetExecutable(anAvmProgram, aCode))
						!= NULL )
				{
					computeInputEnabledCom(activityExec, inputEnabledCom,
							activityExec->getOnIAbort(), isCom,
							hasMutableSchedule );
				}

				break;
			}
			case AVM_OPCODE_ABORT_INVOKE:
			{
				if( (activityExec = StatementFactory::
						getActivityTargetExecutable(anAvmProgram, aCode))
						!= NULL )
				{
					computeInputEnabledCom(activityExec, inputEnabledCom,
							activityExec->getOnAbort(), isCom,
							hasMutableSchedule );
				}

				break;
			}


			// Justification of these switch statement
//			switch( ( anAvmProgram->isScopeTransition() &&
//					(not OperatorManager::isSchedule(aCode->getOperator())) ) ?
//							AVM_OPCODE_NULL : aCode->getAvmOpCode() )

			case AVM_OPCODE_SEQUENCE:
			case AVM_OPCODE_ATOMIC_SEQUENCE:
			case AVM_OPCODE_SEQUENCE_SIDE:
			case AVM_OPCODE_PRIOR_GT:
			{
				ListOfInstanceOfPort localPorts;

				AvmCode::const_iterator itArg = aCode->begin();
				AvmCode::const_iterator itEndArg = aCode->end();
				for( ; itArg != itEndArg ; ++itArg )
				{
					if( (*itArg).is< AvmCode >() )
					{
						computeInputEnabledCom( anAvmProgram, localPorts,
								(*itArg).to_ptr< AvmCode >(), isCom,
								hasMutableSchedule );

						if( localPorts.nonempty() )
						{
							inputEnabledCom.add_union(localPorts);

							break;
						}
					}
				}
				break;
			}

			case AVM_OPCODE_PRIOR_LT:
			{
				ListOfInstanceOfPort localPorts;

				AvmCode::const_reverse_iterator itArg = aCode->rbegin();
				AvmCode::const_reverse_iterator itEndArg = aCode->rend();
				for( ; itArg != itEndArg ; ++itArg )
				{
					if( (*itArg).is< AvmCode >() )
					{
						computeInputEnabledCom( anAvmProgram, localPorts,
								(*itArg).to_ptr< AvmCode >(), isCom,
								hasMutableSchedule );

						if( localPorts.nonempty() )
						{
							inputEnabledCom.add_union(localPorts);

							break;
						}
					}
				}
				break;
			}

			default:
			{
				if( OperatorManager::isSchedule(aCode->getOperator()) )
				{
					AvmCode::const_iterator itArg = aCode->begin();
					AvmCode::const_iterator itEndArg = aCode->end();
					for( ; itArg != itEndArg ; ++itArg )
					{
						if( (*itArg).is< AvmCode >() )
						{
							computeInputEnabledCom(
									anAvmProgram, inputEnabledCom,
									(*itArg).to_ptr< AvmCode >(), isCom,
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
		AvmCode * aCode, bool (*isCom)(AvmCode * comCode) )
{
	if( aCode == NULL )
	{
		//!! NOTHING
		return;
	}
	else if( isCom(aCode) )
	{
		if( aCode->first().is< InstanceOfPort >() )
		{
			inputEnabledCom.add_union(
					aCode->first().to_ptr< InstanceOfPort >() );
		}
	}
	else
	{
		RuntimeID activityRID;

		switch( aCode->getAvmOpCode() )
		{
			case AVM_OPCODE_SCHEDULE_INVOKE:
			{
				if( (activityRID = StatementFactory::
						getActivityTargetRID(anED, aRID, aCode)).valid() )
				{
					if( activityRID.getExecutable()->isMutableSchedule() )
					{
						computeInputEnabledCom(anED, activityRID, inputEnabledCom,
							anED.getRuntimeFormOnSchedule(activityRID), isCom);
					}
					else
					{
						computeInputEnabledCom(anED, activityRID, inputEnabledCom,
								activityRID.getExecutable()->getOnSchedule(),
								isCom );
					}
				}

				break;
			}

			case AVM_OPCODE_INVOKE_TRANSITION:
			{
				// Pour éviter les récursions infinis !!!
				if( isCom == (& CommunicationDependency::isInputEnabledCom) )
				{
					inputEnabledCom.add_union( aCode->first().
							to_ptr< AvmProgram >()->getInputEnabledCom() );
				}
				else if( isCom == (& CommunicationDependency::isInputEnabledSave) )
				{
					inputEnabledCom.add_union( aCode->first().
							to_ptr< AvmProgram >()->getInputEnabledSave() );
				}

				else if( isCom == (& CommunicationDependency::isInputCom) )
				{
					inputEnabledCom.add_union( aCode->first().
							to_ptr< AvmProgram >()->getInputCom() );
				}
				else if( isCom == (& CommunicationDependency::isOutputCom) )
				{
					inputEnabledCom.add_union( aCode->first().
							to_ptr< AvmProgram >()->getOutputCom() );
				}

				else
				{
					computeInputEnabledCom(anED, activityRID, inputEnabledCom,
						aCode->first().to_ptr< AvmProgram >()->getCode(), isCom);
				}

				break;
			}

			case AVM_OPCODE_IRUN:
			{
				if( (activityRID = StatementFactory::
						getActivityTargetRID(anED, aRID, aCode)).valid() )
				{
					computeInputEnabledCom(anED, activityRID, inputEnabledCom,
							activityRID.getExecutable()->getOnIRun(), isCom );
				}

				break;
			}
			case AVM_OPCODE_RUN:
			{
				if( (activityRID = StatementFactory::
						getActivityTargetRID(anED, aRID, aCode)).valid() )
				{
					computeInputEnabledCom(anED, activityRID, inputEnabledCom,
							activityRID.getExecutable()->getOnRun(), isCom );
				}

				break;
			}
			case AVM_OPCODE_RTC:
			{
				if( (activityRID = StatementFactory::
						getActivityTargetRID(anED, aRID, aCode)) != NULL )
				{
					computeInputEnabledCom(anED, activityRID, inputEnabledCom,
							activityRID.getExecutable()->getOnRtc(), isCom );
				}

				break;
			}

			case AVM_OPCODE_IENABLE_INVOKE:
			{
				if( (activityRID = StatementFactory::
						getActivityTargetRID(anED, aRID, aCode)).valid() )
				{
					computeInputEnabledCom(anED, activityRID, inputEnabledCom,
							activityRID.getExecutable()->getOnIEnable(),
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
							activityRID.getExecutable()->getOnEnable(),
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
							activityRID.getExecutable()->getOnIDisable(),
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
							activityRID.getExecutable()->getOnDisable(),
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
							activityRID.getExecutable()->getOnIAbort(),
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
							activityRID.getExecutable()->getOnAbort(), isCom );
				}

				break;
			}


			case AVM_OPCODE_SEQUENCE:
			case AVM_OPCODE_ATOMIC_SEQUENCE:
			case AVM_OPCODE_SEQUENCE_SIDE:
			case AVM_OPCODE_PRIOR_GT:
			{
				ListOfInstanceOfPort localPorts;

				AvmCode::const_iterator itArg = aCode->begin();
				AvmCode::const_iterator itEndArg = aCode->end();
				for( ; itArg != itEndArg ; ++itArg )
				{
					if( (*itArg).is< AvmCode >() )
					{
						computeInputEnabledCom(anED, aRID, localPorts,
								(*itArg).to_ptr< AvmCode >(), isCom );

						if( localPorts.nonempty() )
						{
							inputEnabledCom.add_union(localPorts);

							break;
						}
					}
				}
				break;
			}

			case AVM_OPCODE_PRIOR_LT:
			{
				ListOfInstanceOfPort localPorts;

				AvmCode::const_reverse_iterator itArg = aCode->rbegin();
				AvmCode::const_reverse_iterator itEndArg = aCode->rend();
				for( ; itArg != itEndArg ; ++itArg )
				{
					if( (*itArg).is< AvmCode >() )
					{
						computeInputEnabledCom(anED, aRID, localPorts,
								(*itArg).to_ptr< AvmCode >(), isCom );

						if( localPorts.nonempty() )
						{
							inputEnabledCom.add_union(localPorts);

							break;
						}
					}
				}
				break;
			}

			default:
			{
				if( OperatorManager::isSchedule(aCode->getOperator()) )
				{
					AvmCode::const_iterator itArg = aCode->begin();
					AvmCode::const_iterator itEndArg = aCode->end();
					for( ; itArg != itEndArg ; ++itArg )
					{
						if( (*itArg).is< AvmCode >() )
						{
							computeInputEnabledCom(
									anED, aRID, inputEnabledCom,
									(*itArg).to_ptr< AvmCode >(), isCom );
						}
					}
				}

				break;
			}
		}
	}
}


} /* namespace sep */
