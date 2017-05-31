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

#include "AvmActivityPrimitive.h"

#include <builder/Loader.h>

#include <computer/primitive/AvmSynchronizationFactory.h>

#include <computer/ExecutionEnvironment.h>
#include <computer/ExecutionDataFactory.h>

#include <fml/buffer/BaseBufferForm.h>

#include <fml/executable/ExecutableLib.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/ExpressionConstructor.h>
#include <fml/expression/StatementFactory.h>

#include <fml/operator/OperatorManager.h>

#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/ExecutionConfiguration.h>
#include <fml/runtime/ExecutionSynchronizationPoint.h>
#include <fml/runtime/RuntimeDef.h>
#include <fml/runtime/RuntimeID.h>


namespace sep
{


/**
 ***************************************************************************
 * execution of an CONTEXT_SWITCHER program
 ***************************************************************************
 */
bool AvmPrimitive_ContextSwitcher::run(ExecutionEnvironment & ENV)
{
	RuntimeID saveRID = ENV.mARG->outED->mRID;

	ExecutionEnvironment tmpENV(ENV, ENV.mARG->outED,
			ENV.mARG->at(0).bfRID(), ENV.mARG->at(1).bfCode() );

	if( tmpENV.run() )
	{
		if( tmpENV.outEDS.nonempty() )
		{
			tmpENV.restoreContext( saveRID );

			ENV.spliceOutput( tmpENV );
		}
	}
	else
	{
		return( false );
	}

	return( true );
}


/**
 ***************************************************************************
 * execution of an INIT program
 ***************************************************************************
 */
bool AvmPrimitive_Init::run(ExecutionEnvironment & ENV)
{
	const RuntimeID & tmpRID = ENV.mARG->at(0).bfRID();

	if( ENV.mARG->outED->isDestroyed( tmpRID ) )
	{
		return( true );
	}
	else if( ENV.mARG->outED->isRunnable( tmpRID ) )
	{
		if( tmpRID.getExecutable()->hasOnInit() )
		{
			ExecutionEnvironment tmpENV(ENV, ENV.mARG->outED,
					tmpRID, tmpRID.getExecutable()->getOnInit());

			if( tmpENV.run(PROCESS_INITING_STATE) )
			{
				ENV.spliceNotOutput(tmpENV);

				if( not ENV.appendOutput_mwsetPES_mwsetAEES(tmpENV, tmpRID,
						PROCESS_INITING_STATE, PROCESS_IDLE_STATE) )
				{
					return( false );
				}
			}
			else
			{
				return( false );
			}
		}
		else if( not ENV.appendOutput_mwsetPES(
				ENV.mARG->outED, tmpRID, PROCESS_IDLE_STATE) )
		{
			return( false );
		}
	}
	else
	{
		if( not ENV.mARG->outED->hasRunnableElementTrace() )
//		if( ENV.mARG->outED->isCreated( tmpRID ) )
		{
			ENV.mARG->outED->mAEES = AEES_STMNT_NOTHING;
		}

		ENV.outEDS.append( ENV.mARG->outED );
	}

	return( true );
}


/**
 ***************************************************************************
 * execution of a FINAL program
 ***************************************************************************
 */
bool AvmPrimitive_Final::run(ExecutionEnvironment & ENV)
{
	const RuntimeID & tmpRID = ENV.mARG->at(0).bfRID();

	if( ENV.mARG->outED->isunRunnable( tmpRID ) )
	{
		return( true );
	}
	else if( ENV.mARG->outED->isRunnable( tmpRID ) )
	{
		if( tmpRID.getExecutable()->hasOnFinal() )
		{
			ExecutionEnvironment tmpENV(ENV, ENV.mARG->outED, tmpRID,
					tmpRID.getExecutable()->getOnFinal());

			if( tmpENV.run(PROCESS_FINALIZING_STATE) )
			{
				if( finalizedParent(ENV, tmpENV, tmpRID) )
				{
					ENV.spliceNotOutput(tmpENV);

					return( true );
				}
			}
		}
		else
		{
			if( finalizedParent(ENV, ENV.mARG->outED, tmpRID) )
			{
				return( true );
			}
		}
	}
	else
	{
		ENV.outEDS.append( ENV.mARG->outED );

		return( true );
	}

	return( false );
}


bool AvmPrimitive_Final::finalizedParent(ExecutionEnvironment & ENV,
		ExecutionEnvironment & tmpENV, const RuntimeID & aRID)
{
	ListOfAPExecutionData::iterator itED = tmpENV.outEDS.begin();
	ListOfAPExecutionData::iterator endED = tmpENV.outEDS.end();
	for( ; itED != endED ; ++itED )
	{
		if( not finalizedParent(ENV, (*itED), aRID) )
		{
			return( false );
		}
	}

	return( true );
}


bool AvmPrimitive_Final::finalizedParent(ExecutionEnvironment & ENV,
		APExecutionData & anED, const RuntimeID & aRID)
{
	anED.mwsetRuntimeFormState(aRID, PROCESS_FINALIZED_STATE);

	anED->setAEES( RuntimeDef::PES_to_AEES(
			PROCESS_FINALIZED_STATE, anED->getAEES()) );

	List< RuntimeID > runnableRID;

	RuntimeID tmpRID = aRID;
	bool finalizeSelf;

	while( (tmpRID = tmpRID.getPRID()).valid() )
	{
		const RuntimeForm & tmpRF = anED->getRuntime(tmpRID);
		finalizeSelf = false;

		AVM_OS_ASSERT_FATAL_ERROR_EXIT( tmpRF.hasChild() )
				<< "Unexpectded PRID RF with out child :> \n"
				<< tmpRF.toString( AVM_TAB1_INDENT )
				<< SEND_EXIT;

		if( tmpRID.getSpecifier().isMocCompositeStructure() )
		{
			TableOfRuntimeID::const_iterator it = tmpRF.beginChild();
			TableOfRuntimeID::const_iterator endIt = tmpRF.endChild();
			for( ; it != endIt ; ++it )
			{
				if( not anED->isFinalizedOrDestroyed(*it) )
				{
					ENV.outEDS.append( anED );

					return( true );
				}
			}
			finalizeSelf = true;
		}
		else
		{
			StatementFactory::collectRID(tmpRF.getOnSchedule(), runnableRID);

			List< RuntimeID >::const_iterator it = runnableRID.begin();
			List< RuntimeID >::const_iterator endIt = runnableRID.end();
			for( ; it != endIt ; ++it )
			{
				if( not anED->isFinalizedOrDestroyed(*it) )
				{
					ENV.outEDS.append( anED );

					return( true );
				}
			}
			finalizeSelf = true;
		}

		if( finalizeSelf )
		{
			if( tmpRID.getExecutable()->hasOnFinal() )
			{
				ExecutionEnvironment tmpENV(ENV, anED, tmpRID,
						tmpRID.getExecutable()->getOnFinal());

				if( tmpENV.run(PROCESS_FINALIZING_STATE) )
				{
					if( finalizedParent(ENV, tmpENV, tmpRID) )
					{
						ENV.spliceNotOutput(tmpENV);

						return( true );
					}
				}

				return( false );
			}
			else
			{
				ENV.mwsetPES_mwsetAEES(anED, tmpRID, PROCESS_FINALIZED_STATE);
			}
		}
	}

	if( tmpRID.invalid() )
	{
		if( anED->isunRunnableSystem() )
		{
			anED->setAEES(AEES_STMNT_EXIT);
			ENV.exitEDS.append( anED );
		}
		else
		{
			ENV.outEDS.append( anED );
		}
	}
	else
	{
		ENV.outEDS.append( anED );
	}

	return( true );
}



/**
 ***************************************************************************
 * execution of an DESTROY program
 ***************************************************************************
 */
bool AvmPrimitive_Destroy::run(ExecutionEnvironment & ENV)
{
	const RuntimeID & tmpRID = ENV.mARG->at(0).bfRID();

	if( ENV.mARG->outED->isunRunnable( tmpRID ) )
	{
		return( true );
	}
	else if( ENV.mARG->outED->isRunnable( tmpRID ) )
	{
		if( tmpRID.getExecutable()->hasOnFinal() )
		{
			ExecutionEnvironment tmpENV(ENV, ENV.mARG->outED, tmpRID,
					tmpRID.getExecutable()->getOnFinal());

			if( tmpENV.run(PROCESS_FINALIZING_STATE) )
			{
				if( destroyedParent(ENV, tmpENV, tmpRID) )
				{
					ENV.spliceNotOutput(tmpENV);

					return( true );
				}
			}
		}
		else
		{
			if( destroyedParent(ENV, ENV.mARG->outED, tmpRID) )
			{
				return( true );
			}
		}
	}
	else
	{
		ENV.outEDS.append( ENV.mARG->outED );

		return( true );
	}

	return( false );
}


bool AvmPrimitive_Destroy::destroyedParent(ExecutionEnvironment & ENV,
		ExecutionEnvironment & tmpENV, const RuntimeID & aRID)
{
	ListOfAPExecutionData::iterator itED = tmpENV.outEDS.begin();
	ListOfAPExecutionData::iterator endED = tmpENV.outEDS.end();
	for( ; itED != endED ; ++itED )
	{
		if( not destroyedParent(ENV, (*itED), aRID) )
		{
			return( false );
		}
	}

	return( true );
}


bool AvmPrimitive_Destroy::destroyedParent(ExecutionEnvironment & ENV,
		APExecutionData & anED, const RuntimeID & aRID)
{
	anED.mwsetRuntimeFormState(aRID, PROCESS_DESTROYED_STATE);
	if( aRID.hasModel() )
	{
		anED->getWritableRuntime( aRID.getModel() ).decrInstanciationCount();
	}

	anED->setAEES( RuntimeDef::PES_to_AEES(
			PROCESS_DESTROYED_STATE, anED->getAEES()) );

	RuntimeID tmpRID = aRID;
	bool autoDestroy;

	while( (tmpRID = tmpRID.getPRID()).valid() )
	{
		const RuntimeForm & tmpRF = anED->getRuntime(tmpRID);
		autoDestroy = false;

		AVM_OS_ASSERT_FATAL_ERROR_EXIT( tmpRF.hasChild() )
				<< "Unexpectded PRID RF with out child :> \n"
				<< tmpRF.toString( AVM_TAB1_INDENT )
				<< SEND_EXIT;

		if( tmpRID.getSpecifier().isMocCompositeStructure() )
		{
			TableOfRuntimeID::const_iterator it = tmpRF.beginChild();
			TableOfRuntimeID::const_iterator endIt = tmpRF.endChild();
			for( ; it != endIt ; ++it )
			{
				if( not anED->isFinalizedOrDestroyed(*it) )
				{
					ENV.outEDS.append( anED );

					return( true );
				}
			}
			autoDestroy = true;
		}
		else
		{
			autoDestroy = true;
		}

		if( autoDestroy )
		{
			if( tmpRID.getExecutable()->hasOnFinal() )
			{
				ExecutionEnvironment tmpENV(ENV, anED, tmpRID,
						tmpRID.getExecutable()->getOnFinal());

				if( tmpENV.run(PROCESS_FINALIZING_STATE) )
				{
					if( destroyedParent(ENV, tmpENV, tmpRID) )
					{
						ENV.spliceNotOutput(tmpENV);

						return( true );
					}
				}

				return( false );
			}
			else
			{
				ENV.mwsetPES_mwsetAEES(anED, tmpRID, PROCESS_DESTROYED_STATE);
				if( tmpRID.hasModel() )
				{
					anED->getWritableRuntime(
							tmpRID.getModel() ).decrInstanciationCount();
				}
			}
		}
	}

	if( tmpRID.invalid() )
	{
		if( anED->isunRunnableSystem() )
		{
			anED->setAEES(AEES_STMNT_EXIT);
			ENV.exitEDS.append( anED );
		}
		else
		{
			ENV.outEDS.append( anED );
		}
	}
	else
	{
		ENV.outEDS.append( anED );
	}

	return( true );
}


/**
 ***************************************************************************
 * execution of a START program
 ***************************************************************************
 */
bool AvmPrimitive_Start::run(ExecutionEnvironment & ENV)
{
	const RuntimeID & tmpRID = ENV.mARG->at(0).bfRID();

	if( ENV.mARG->outED->isDestroyed( tmpRID ) )
	{
		return( true );
	}
	else if( ENV.mARG->outED->isCreatedOrRunnable( tmpRID ) ||
			ENV.mARG->outED->isFinalized( tmpRID ) )
	{
		BFCode aProgram = tmpRID.getOnStart();
		if( aProgram.invalid() )
		{
			aProgram = tmpRID.getExecutable()->getOnStart();

			if( aProgram.invalid() )
			{
				aProgram = tmpRID.getExecutable()->getOnInit();
			}
		}

		if( aProgram.valid() )
		{
			ExecutionEnvironment tmpENV(ENV, ENV.mARG->outED, tmpRID, aProgram);

			if( tmpENV.run(PROCESS_STARTING_STATE) )
			{
				ENV.spliceNotOutput(tmpENV);

				if( not ENV.appendOutput_mwsetPES_mwsetAEES(tmpENV, tmpRID,
						PROCESS_STARTING_STATE, PROCESS_IDLE_STATE) )
				{
					return( false );
				}
			}
			else
			{
				return( false );
			}
		}
		else if( not ENV.appendOutput_mwsetPES(
				ENV.mARG->outED, tmpRID, PROCESS_IDLE_STATE) )
		{
			return( false );
		}
	}
	else
	{
		ENV.outEDS.append( ENV.mARG->outED );
	}

	return( true );
}


/**
 ***************************************************************************
 * execution of a RESTART program
 ***************************************************************************
 */
bool AvmPrimitive_Restart::run(ExecutionEnvironment & ENV)
{
	BFCode aProgram = ENV.inCODE;

	ExecutionEnvironment tmpENV(ENV, aProgram);

	if( tmpENV.run(OperatorManager::OPERATOR_STOP) )
	{
		if( tmpENV.runFromOutputs(OperatorManager::OPERATOR_START, aProgram) )
		{
			ENV.spliceOutput( tmpENV );

			return( true );
		}
	}

	return( false );
}


/**
 ***************************************************************************
 * execution of a STOP program
 ***************************************************************************
 */
bool AvmPrimitive_Stop::run(ExecutionEnvironment & ENV)
{
	const RuntimeID & tmpRID = ENV.mARG->at(0).bfRID();

	if( ENV.mARG->outED->isunRunnable( tmpRID ) )
	{
		return( true );
	}
	else if( ENV.mARG->outED->isRunnable( tmpRID ) )
	{
		if( tmpRID.getExecutable()->hasOnStop() )
		{
			ExecutionEnvironment tmpENV(ENV, ENV.mARG->outED, tmpRID,
					tmpRID.getExecutable()->getOnStop());

			if( tmpENV.run(PROCESS_STOPPING_STATE) )
			{
				ENV.spliceNotOutput(tmpENV);

				if( not ENV.appendOutput_mwsetPES_mwsetAEES(tmpENV, tmpRID,
						PROCESS_STOPPING_STATE, PROCESS_STOPPED_STATE) )
				{
					return( false );
				}
			}
			else
			{
				return( false );
			}
		}
		else if( not ENV.appendOutput_mwsetPES(
				ENV.mARG->outED, tmpRID, PROCESS_STOPPED_STATE) )
		{
			return( false );
		}
	}
	else
	{
		ENV.outEDS.append( ENV.mARG->outED );
	}

	return( true );
}



/**
 ***************************************************************************
 * execution of a WAIT program
 ***************************************************************************
 */
bool AvmPrimitive_Wait::run(ExecutionEnvironment & ENV)
{
	const RuntimeID & tmpRID = ENV.mARG->at(0).bfRID();

	ENV.mARG->outED.mwsetRuntimeFormState(tmpRID, PROCESS_WAITING_STATE);

	ENV.outEDS.append( ENV.mARG->outED );

	return( true );
}



/**
 ***************************************************************************
 * execution of a SUSPEND program
 ***************************************************************************
 */

bool AvmPrimitive_Suspend::run(ExecutionEnvironment & ENV)
{
	const RuntimeID & tmpRID = ENV.mARG->at(0).bfRID();

	if( ENV.mARG->outED->isunRunnable( tmpRID ) )
	{
		return( true );
	}

	ENV.mARG->outED.mwsetRuntimeFormState(tmpRID, PROCESS_SUSPENDED_STATE);

	ENV.outEDS.append( ENV.mARG->outED );

	return( true );
}



/**
 ***************************************************************************
 * execution of a RESUME program
 ***************************************************************************
 */
bool AvmPrimitive_Resume::run(ExecutionEnvironment & ENV)
{
	const RuntimeID & tmpRID = ENV.mARG->at(0).bfRID();

	if( ENV.mARG->outED->isSuspended( tmpRID ) )
	{
		ENV.mARG->outED.mwsetRuntimeFormState(tmpRID, PROCESS_IDLE_STATE);

		ENV.outEDS.append( ENV.mARG->outED );
	}

	return( true );
}



/**
 ***************************************************************************
 * execution of an IENABLE program
 ***************************************************************************
 */
bool AvmPrimitive_IEnableInvoke::run(ExecutionEnvironment & ENV)
{
	ENV.mARG->outED.makeWritable();

	ENV.mARG->outED->mRID = ENV.mARG->at(0).bfRID();

	const BFCode & onInvoke =
			ENV.mARG->outED->mRID.getExecutable()->getOnIEnable();
	if( onInvoke.valid() )
	{

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , PROGRAM )
	ExecutionDataFactory::appendRunnableElementTrace(ENV.mARG->outED,
			BF(new ExecutionConfiguration(ENV.mARG->outED->mRID,
					CONST_BF_OPERATOR(IENABLE_INVOKE))));
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , PROGRAM )

		return( ENV.run(ENV.mARG->outED, onInvoke) );
	}
	else
	{
		ENV.appendOutput( ENV.mARG->outED );

		return( true );
	}
}


/**
 ***************************************************************************
 * execution of an ENABLE program
 ***************************************************************************
 */
bool AvmPrimitive_EnableInvoke::run(ExecutionEnvironment & ENV)
{
	ENV.mARG->outED.makeWritable();
	ENV.mARG->outED->mPreserveRID = true;

	ENV.mARG->outED->mRID = ENV.mARG->at(0).bfRID();

//	ENV.mARG->outED.mwsetRuntimeFormOnScheduleAndIdle(ENV.mARG->outED->mRID);

	const BFCode & onInvoke =
			ENV.mARG->outED->mRID.getExecutable()->getOnEnable();
	if( onInvoke.valid() )
	{

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , PROGRAM )
	ExecutionDataFactory::appendRunnableElementTrace(ENV.mARG->outED,
			BF(new ExecutionConfiguration(ENV.mARG->outED->mRID,
					CONST_BF_OPERATOR(ENABLE_INVOKE))));
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , PROGRAM )

		return( ENV.run(ENV.mARG->outED, onInvoke) );
	}
	else
	{
		ENV.appendOutput( ENV.mARG->outED );

		return( true );
	}
}


/**
 ***************************************************************************
 * execution of an ENABLE#SET program
 ***************************************************************************
 */
bool AvmPrimitive_EnableSet::run(ExecutionEnvironment & ENV)
{
	ENV.mARG->outED.makeWritable();
	ENV.mARG->outED->mPreserveRID = true;

	ENV.mARG->outED->mRID = ENV.mARG->at(0).bfRID();

	ENV.mARG->outED.mwsetRuntimeFormOnScheduleAndIdle(ENV.mARG->outED->mRID);

	ENV.appendOutput( ENV.mARG->outED );

	return( true );
}



/**
 ***************************************************************************
 * execution of a GOTO program
 ***************************************************************************
 */
bool AvmPrimitive_Goto::run(ExecutionEnvironment & ENV)
{
	AVM_OS_FATAL_ERROR_EXIT
			<< "AvmPrimitive_Goto::run:> Unexpected GOTO< STATEMENT > !!!"
			<< SEND_EXIT;

//	if( ENV.run( StatementConstructor::newCode(
//			OperatorManager::OPERATOR_DISABLE, ENV.mARG->outED->mRID) ) )
//	{
//		return( ENV.runFromOutputs( StatementConstructor::newCode(
//				OperatorManager::OPERATOR_ENABLE, ENV.mARG->at(0)) ) );
//	}

	return( false );
}



/**
 ***************************************************************************
 * execution of a IDISABLE program
 ***************************************************************************
 */
bool AvmPrimitive_IDisableInvoke::run(ExecutionEnvironment & ENV)
{
	ENV.mARG->outED.makeWritable();

	ENV.mARG->outED->mRID = ENV.mARG->at(0).bfRID();

	const BFCode & onInvoke =
			ENV.mARG->outED->mRID.getExecutable()->getOnIDisable();
	if( onInvoke.valid() )
	{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , PROGRAM )
	ExecutionDataFactory::appendRunnableElementTrace(ENV.mARG->outED,
			BF(new ExecutionConfiguration(ENV.mARG->outED->mRID,
					CONST_BF_OPERATOR(IDISABLE_INVOKE))));
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , PROGRAM )

		return( ENV.run(ENV.mARG->outED, onInvoke) );
	}
	else
	{
		ENV.outEDS.append( ENV.mARG->outED );

		return( true );
	}
}


/**
 ***************************************************************************
 * execution of a DISABLE program
 ***************************************************************************
 */
bool AvmPrimitive_DisableInvoke::run(ExecutionEnvironment & ENV)
{
	ENV.mARG->outED.makeWritable();
	ENV.mARG->outED->mPreserveRID = true;

	ENV.mARG->outED->mRID = ENV.mARG->at(0).bfRID();

	const BFCode & onInvoke =
			ENV.mARG->outED->mRID.getExecutable()->getOnDisable();
	if( onInvoke.valid() )
	{

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , PROGRAM )
	ExecutionDataFactory::appendRunnableElementTrace(ENV.mARG->outED,
			BF(new ExecutionConfiguration(ENV.mARG->outED->mRID,
					CONST_BF_OPERATOR(DISABLE_INVOKE))));
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , PROGRAM )

		return( ENV.run(ENV.mARG->outED, onInvoke) );
	}
	else
	{
		ENV.mARG->outED.mwsetRuntimeFormState(PROCESS_DISABLED_STATE);

		ENV.mARG->outED->mRID = ENV.mARG->outED->mRID.getPRID();

		ENV.outEDS.append( ENV.mARG->outED );

		return( true );
	}
}


/**
 ***************************************************************************
 * execution of a DISABLE#SET program
 ***************************************************************************
 */
bool AvmPrimitive_DisableSet::run(ExecutionEnvironment & ENV)
{
	ENV.mARG->outED.makeWritable();
	ENV.mARG->outED->mPreserveRID = true;

	ENV.mARG->outED->mRID = ENV.mARG->at(0).bfRID();

	ENV.mARG->outED.mwsetRuntimeFormState(PROCESS_DISABLED_STATE);

	ENV.mARG->outED->mRID = ENV.mARG->outED->mRID.getPRID();

	ENV.outEDS.append( ENV.mARG->outED );

	return( true );
}



/**
 ***************************************************************************
 * execution of a DISABLE#CHILD program
 ***************************************************************************
 */
bool AvmPrimitive_DisableChild::run(ExecutionEnvironment & ENV)
{
	APExecutionData outED = ENV.inED;
	outED.makeWritable();
	outED->mPreserveRID = true;

//	const BFCode & onDisable = ENV.inED->mRID.getExecutable()->getOnDisable();
//	if( onDisable.valid() )
//	{
//AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , PROGRAM )
//	ExecutionDataFactory::appendRunnableElementTrace(outED,
//		BF(new ExecutionConfiguration(outED->mRID, CONST_BF_OPERATOR(DISABLE))));
//AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , PROGRAM )
//
//		ExecutionEnvironment tmpENV(ENV, outED, outED->mRID);
//		if( tmpENV.run(onDisable) )
//		{
//			while( tmpENV.outEDS.nonempty() )
//			{
//				tmpENV.outEDS.pop_first_to( outED );
//
//				outED.mwsetRuntimeFormState(ENV.inED->mRID,
//						PROCESS_DISABLED_STATE);
//
//				outED->mRID = ENV.inED->mRID.getPRID();
//
//				ENV.outEDS.append( outED );
//			}
//
//			ENV.spliceNotOutput( tmpENV );
//		}
//		else
//		{
//			return( false );
//		}
//	}
//	else
	{
		outED.mwsetRuntimeFormState(PROCESS_DISABLED_STATE);

//		outED->mRID = ENV.inED->mRID.getPRID();

		ENV.outEDS.append( outED );
	}

	return( true );
}



/**
 ***************************************************************************
 * execution of a DISABLE#SELF program
 ***************************************************************************
 */
bool AvmPrimitive_DisableSelf::run(ExecutionEnvironment & ENV)
{
	APExecutionData outED = ENV.inED;
	outED.makeWritable();
	outED->mPreserveRID = true;

	outED.mwsetRuntimeFormState(PROCESS_DISABLED_STATE);

	outED->mRID = ENV.inED->mRID.getPRID();

	ENV.outEDS.append( outED );

	return( true );
}



/**
 ***************************************************************************
 * execution of a DISABLE#SELVES program
 ***************************************************************************
 */
bool AvmPrimitive_DisableSelves::run(ExecutionEnvironment & ENV)
{
	ENV.mARG->outED.makeWritable();
	ENV.mARG->outED->mPreserveRID = true;

	for( avm_uinteger_t level = ENV.mARG->at(0).toInteger() ;
			level > 0 ; --level )
	{
		ENV.mARG->outED.mwsetRuntimeFormState(PROCESS_DISABLED_STATE);

		ENV.mARG->outED->mRID = ENV.mARG->outED->mRID.getPRID();
	}

	ENV.outEDS.append( ENV.mARG->outED );

	return( true );
}




/**
 ***************************************************************************
 * execution of a IABORT program
 ***************************************************************************
 */
bool AvmPrimitive_IAbortInvoke::run(ExecutionEnvironment & ENV)
{
	ENV.mARG->outED.makeWritable();

	ENV.mARG->outED->mRID = ENV.mARG->at(0).bfRID();

	const BFCode & onInvoke =
			ENV.mARG->outED->mRID.getExecutable()->getOnIAbort();
	if( onInvoke.valid() )
	{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , PROGRAM )
	ExecutionDataFactory::appendRunnableElementTrace(ENV.mARG->outED,
			BF(new ExecutionConfiguration(ENV.mARG->outED->mRID,
					CONST_BF_OPERATOR(IABORT_INVOKE))));
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , PROGRAM )

		return( ENV.run(ENV.mARG->outED, onInvoke) );
	}
	else
	{
		ENV.outEDS.append( ENV.mARG->outED );

		return( true );
	}
}


bool AvmPrimitive_AbortInvoke::run(ExecutionEnvironment & ENV)
{
	ENV.mARG->outED.makeWritable();
	ENV.mARG->outED->mPreserveRID = true;

	ENV.mARG->outED->mRID = ENV.mARG->at(0).bfRID();

	const BFCode & onInvoke = ENV.mARG->outED->mRID.getExecutable()->getOnAbort();
	if( onInvoke.valid() )
	{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , PROGRAM )
	ExecutionDataFactory::appendRunnableElementTrace(ENV.mARG->outED,
			BF(new ExecutionConfiguration(ENV.mARG->outED->mRID,
					CONST_BF_OPERATOR(ABORT_INVOKE))));
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , PROGRAM )

		return( ENV.run(ENV.mARG->outED, onInvoke) );
	}
	else
	{
		ENV.mARG->outED.mwsetRuntimeFormState(PROCESS_ABORTED_STATE);

		ENV.mARG->outED->mRID = ENV.mARG->outED->mRID.getPRID();

		ENV.outEDS.append( ENV.mARG->outED );

		return( true );
	}
}


/**
 ***************************************************************************
 * execution of a ABORT#SET program
 ***************************************************************************
 */
bool AvmPrimitive_AbortSet::run(ExecutionEnvironment & ENV)
{
	RuntimeID anActiveID = ENV.mARG->outED->mRID;

	ENV.mARG->outED.makeWritable();
	ENV.mARG->outED->mPreserveRID = true;

	ENV.mARG->outED->mRID = ENV.mARG->at(0).bfRID();

	ENV.mARG->outED.mwsetRuntimeFormState(PROCESS_ABORTED_STATE);

	ENV.mARG->outED->mRID = ENV.mARG->outED->mRID.getPRID();

	ENV.outEDS.append( ENV.mARG->outED );

	return( true );
}



/**
 ***************************************************************************
 * execution of a ABORT#CHILD program
 ***************************************************************************
 */
bool AvmPrimitive_AbortChild::run(ExecutionEnvironment & ENV)
{
	APExecutionData outED = ENV.inED;
	outED.makeWritable();
	outED->mPreserveRID = true;

//	const BFCode & onAbort = ENV.inED->mRID.getExecutable()->getOnAbort();
//	if( onAbort.valid() )
//	{
//AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , PROGRAM )
//	ExecutionDataFactory::appendRunnableElementTrace(outED,
//		BF(new ExecutionConfiguration(outED->mRID, CONST_BF_OPERATOR(ABORT))));
//AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , PROGRAM )
//
//		ExecutionEnvironment tmpENV(ENV, outED, outED->mRID);
//		if( tmpENV.run(onAbort) )
//		{
//			while( tmpENV.outEDS.nonempty() )
//			{
//				tmpENV.outEDS.pop_first_to( outED );
//
//				outED.mwsetRuntimeFormState(ENV.inED->mRID,
//						PROCESS_ABORTED_STATE);
//
//				outED->mRID = ENV.inED->mRID.getPRID();
//
//				ENV.outEDS.append( outED );
//			}
//
//			ENV.spliceNotOutput(tmpENV);
//		}
//		else
//		{
//			return( false );
//		}
//	}
//	else
	{
		outED.mwsetRuntimeFormState(PROCESS_ABORTED_STATE);

//		outED->mRID = ENV.inED->mRID.getPRID();

		ENV.outEDS.append( outED );
	}

	return( true );
}


/**
 ***************************************************************************
 * execution of a ABORT#SELF program
 ***************************************************************************
 */
bool AvmPrimitive_AbortSelf::run(ExecutionEnvironment & ENV)
{
	APExecutionData outED = ENV.inED;
	outED.makeWritable();
	outED->mPreserveRID = true;

	outED.mwsetRuntimeFormState(PROCESS_ABORTED_STATE);

	outED->mRID = ENV.inED->mRID.getPRID();

	ENV.outEDS.append( outED );

	return( true );
}


/**
 ***************************************************************************
 * execution of a ABORT#SELVES program
 ***************************************************************************
 */
bool AvmPrimitive_AbortSelves::run(ExecutionEnvironment & ENV)
{
	ENV.mARG->outED.makeWritable();
	ENV.mARG->outED->mPreserveRID = true;

	for( avm_uinteger_t level = ENV.mARG->at(0).toInteger() ;
			level > 0 ; --level )
	{
		ENV.mARG->outED.mwsetRuntimeFormState(PROCESS_ABORTED_STATE);

		ENV.mARG->outED->mRID = ENV.mARG->outED->mRID.getPRID();
	}

	ENV.outEDS.append( ENV.mARG->outED );

	return( true );
}



/**
 ***************************************************************************
 * execution of an RUN program
 ***************************************************************************
 */
bool AvmPrimitive_Nop::run(ExecutionEnvironment & ENV)
{
	ENV.outEDS.append( ENV.inED );

	return( true );
}



/**
 ***************************************************************************
 * execution of a HISTORY#CLEAR program
 ***************************************************************************
 */
bool AvmPrimitive_HistoryClear::run(ExecutionEnvironment & ENV)
{
	ENV.mARG->outED->mRID = ENV.mARG->at(0).bfRID();

	if( ENV.mARG->outED->mRID.getSpecifier().isMocStateTransitionStructure() )
	{
		ENV.mARG->outED.mwsetRuntimeFormOnSchedule(ENV.mARG->outED->mRID,
				ENV.mARG->outED->mRID.getExecutable()->getOnEnable());
	}

	ENV.outEDS.append( ENV.mARG->outED );

	return( true );
}


/**
 ***************************************************************************
 * execution of a DEEP_HISTORY#INVOKE program <=> SCHEDULE#INVOKE
 ***************************************************************************
 */
bool AvmPrimitive_DeepHistoryInvoke::run(ExecutionEnvironment & ENV)
{
	ENV.mARG->outED->mRID = ENV.mARG->at(0).bfRID();

	if( ENV.mARG->outED->isunRunnable( ENV.mARG->outED->mRID ) )
	{
		return( true );
	}
	else
	{
		const BFCode & onInvoke = ENV.mARG->outED->getRuntimeFormOnSchedule(
				ENV.mARG->outED->mRID);

		if( onInvoke.valid() &&
				ENV.mARG->outED->isRunnable( ENV.mARG->outED->mRID ) )
		{
			ExecutionEnvironment tmpENV(ENV, ENV.mARG->outED, onInvoke);
			if( tmpENV.run(PROCESS_RUNNING_STATE) )
			{
				ENV.spliceOutput(tmpENV);
			}
			else
			{
				return( false );
			}
		}
		else
		{
			ENV.outEDS.append( ENV.mARG->outED );
		}
	}

	return( true );


	ENV.outEDS.append( ENV.mARG->outED );

	return( true );
}


/**
 ***************************************************************************
 * execution of a SHALLOW_HISTORY#INVOKE program <=> SCHEDULE#INVOKE
 ***************************************************************************
 */
bool AvmPrimitive_ShallowHistoryInvoke::run(ExecutionEnvironment & ENV)
{
	ENV.mARG->outED->mRID = ENV.mARG->at(0).bfRID();

	if( ENV.mARG->outED->isunRunnable( ENV.mARG->outED->mRID ) )
	{
		return( true );
	}
	else
	{
		const BFCode & onInvoke = ENV.mARG->outED->getRuntimeFormOnSchedule(
				ENV.mARG->outED->mRID);

		if( onInvoke.valid() &&
				ENV.mARG->outED->isRunnable( ENV.mARG->outED->mRID ) )
		{
			ExecutionEnvironment tmpENV(ENV, ENV.mARG->outED, onInvoke);
			if( tmpENV.run(PROCESS_RUNNING_STATE) )
			{
				ENV.spliceOutput(tmpENV);
			}
			else
			{
				return( false );
			}
		}
		else
		{
			ENV.outEDS.append( ENV.mARG->outED );
		}
	}

	return( true );


	ENV.outEDS.append( ENV.mARG->outED );

	return( true );
}


/**
 ***************************************************************************
 * execution of a IRUN program
 ***************************************************************************
 */
bool AvmPrimitive_IRun::run(ExecutionEnvironment & ENV)
{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , PROGRAM )

//	if( ENV.inED->isRunnable( ) )
	{
		ExecutionDataFactory::appendRunnableElementTrace(ENV.inED,
				BF(new ExecutionConfiguration(ENV.inED->mRID,
						CONST_BF_OPERATOR(IRUN))));

		return( ENV.run() );
	}
//	else
//	{
//		ENV.outEDS.append( ENV.inED );
//		return( true );
//	}
AVM_ELSE

	return( ENV.run() );

AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , PROGRAM )
}


/**
 ***************************************************************************
 * execution of a RUN program
 ***************************************************************************
 */
bool AvmPrimitive_Run::run(ExecutionEnvironment & ENV)
{
	const RuntimeID & tmpRID = ENV.mARG->at(0).bfRID();

	if( ENV.mARG->outED->isunRunnable( tmpRID ) )
	{
		return( true );
	}
	else if( tmpRID.getExecutable()->hasOnRun() &&
			ENV.mARG->outED->isRunnable( tmpRID ) )
	{
		const BFCode & aRunCode = tmpRID.getExecutable()->getOnRun();

		ENV.mARG->outED.mwsetRuntimeFormState(PROCESS_RUNNING_STATE);

		ExecutionEnvironment tmpENV(ENV, ENV.mARG->outED, tmpRID, aRunCode);

//AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , PROGRAM )
	ExecutionDataFactory::appendRunnableElementTrace(tmpENV.inED,
			BF(new ExecutionConfiguration(tmpRID, CONST_BF_OPERATOR(RUN))));

//	AVM_OS_TRACE << "run:> " << tmpRID.str() << std::endl;
//AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , PROGRAM )

		// Execution of Internal Run
		if( tmpRID.getExecutable()->hasOnIRun() )
		{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , PROGRAM )
	ExecutionDataFactory::appendRunnableElementTrace(tmpENV.inED,
			BF(new ExecutionConfiguration(tmpRID, CONST_BF_OPERATOR(IRUN))));
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , PROGRAM )

			if( tmpENV.run(/*OperatorManager::OPERATOR_IRUN,*/
					tmpRID.getExecutable()->getOnIRun()) )
			{
				ENV.spliceNotOutput( tmpENV );

				if( tmpENV.outEDS.nonempty() )
				{
					ListOfAPExecutionData irunEDS( tmpENV.outEDS );

					if( tmpENV.runFromOutputs(aRunCode) )
					{
						if( tmpENV.outEDS.nonempty() )
						{
							ENV.spliceOutput(tmpENV);
						}
						else // Preserve Internal Run effect
						{
							ENV.outEDS.append( irunEDS );
						}

						ENV.spliceNotOutput( tmpENV );
					}
					else
					{
						return( false );
					}
				}
				else
				{
					if( tmpENV.run(aRunCode) )
					{
						APExecutionData tmpED;

						// IRQ EDS traitement
						while( tmpENV.irqEDS.nonempty() )
						{
							tmpENV.irqEDS.pop_last_to( tmpED );

							// Verification of EXECUTION ENDING STATUS
							switch( tmpED->getAEES() )
							{
								case AEES_STMNT_BREAK:
								case AEES_STMNT_CONTINUE:
								case AEES_STMNT_RETURN:
								{
									tmpED.mwsetAEES( AEES_OK );

									ENV.outEDS.append( tmpED );

									break;
								}

								default:
								{
									AVM_OS_FATAL_ERROR_EXIT
											<< "Unexpected ENDIND EXECUTION "
												"STATUS as irqEDS :> "
											<< RuntimeDef::strAEES( tmpED->mAEES )
											<< " !!!"
											<< SEND_EXIT;

									break;
								}
							}
						}

						ENV.spliceOutput(tmpENV);
					}
					else
					{
						return( false );
					}
				}
			}
			else
			{
				return( false );
			}
		}
		else
		{
			if( tmpENV.run() )
			{
				APExecutionData tmpED;

				// IRQ EDS traitement
				while( tmpENV.irqEDS.nonempty() )
				{
					tmpENV.irqEDS.pop_last_to( tmpED );

					// Verification of EXECUTION ENDING STATUS
					switch( tmpED->getAEES() )
					{
						case AEES_STMNT_BREAK:
						case AEES_STMNT_CONTINUE:
						case AEES_STMNT_RETURN:
						{
							tmpED.mwsetAEES( AEES_OK );

							ENV.outEDS.append( tmpED );

							break;
						}

						default:
						{
							AVM_OS_FATAL_ERROR_EXIT
									<< "Unexpected ENDIND EXECUTION STATUS "
										"as irqEDS :> "
									<< RuntimeDef::strAEES( tmpED->mAEES )
									<< " !!!"
									<< SEND_EXIT;

							break;
						}
					}
				}

				ENV.spliceOutput(tmpENV);
			}
			else
			{
				return( false );
			}
		}
	}
	else
	{
		if( not ENV.mARG->outED->hasRunnableElementTrace() )
//		if( ENV.mARG->outED->isCreated( tmpRID ) )
		{
			ENV.mARG->outED->mAEES = AEES_STMNT_NOTHING;
		}

		ENV.appendOutput(ENV.mARG->outED);
	}

	return( true );
}



/**
 ***************************************************************************
 * execution of a RTC program
 ***************************************************************************
 */
bool AvmPrimitive_Rtc::run(ExecutionEnvironment & ENV)
{
	const RuntimeID & rtcRID = ENV.mARG->at(0).bfRID();

	if( ENV.mARG->outED->isunRunnable( rtcRID ) )
	{
		return( true );
	}
	else if( ENV.mARG->outED->isRunnable( rtcRID ) )
	{
		const BFCode rctCode = rtcRID.getExecutable()->getOnRtc();

		ExecutionEnvironment tmpENV(ENV, ENV.mARG->outED, rtcRID, rctCode);

//AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , PROGRAM )
	ExecutionDataFactory::appendRunnableElementTrace(tmpENV.inED,
			BF(new ExecutionConfiguration(rtcRID, CONST_BF_OPERATOR(RTC))));

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , STATEMENT )
	AVM_OS_TRACE << "rtc:> " << rtcRID.str() << std::endl;
	AVM_OS_COUT  << "rtc:> " << rtcRID.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , STATEMENT )

//AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , PROGRAM )

		if( not tmpENV.run(PROCESS_RTC_STATE) )
		{
			return( false );
		}

		if( tmpENV.hasOutput() )
		{
			ListOfAPExecutionData nextRTC;
			ListOfAPExecutionData prevRTC;

			if( tmpENV.extractOtherOutputED(ENV.mARG->outED, prevRTC) )
			{
				if( prevRTC.empty() )
				{
					ENV.appendOutput_wrtAEES( ENV.mARG->outED );
				}
			}

			APExecutionData tmpED;

			while( prevRTC.nonempty() )
			{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , PROGRAM )
	AVM_OS_COUT << "rtc:> leaf count: " << prevRTC.size() << std::endl;

	AVM_OS_COUT << "PRESS ENTER" << std::endl;
	std::cin.get();
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , PROGRAM )

//				currentED.pop_first_to( tmpED );
				prevRTC.pop_last_to( tmpED );

				switch( tmpED->mAEES )
				{
					case AEES_STMNT_NOTHING:
					case AEES_STMNT_CONTINUE:
					case AEES_STMNT_FINAL:
					case AEES_STMNT_DESTROY:
					{
						tmpED.mwsetAEES( AEES_OK );

						//!!! NO << break >> for these statement
					}

					// Evaluation of NEXT SEQUENCIAL STATEMENT
					case AEES_OK:
					case AEES_STEP_RESUME:
					{
						tmpED->mRID = rtcRID;

						if( tmpENV.run(tmpED, rctCode) )
						{
							if( tmpENV.hasOutput() )
							{
								if( tmpENV.extractOtherOutputED(tmpED, nextRTC) )
								{
									if( nextRTC.empty()
										&& tmpED->isTNEQ( ENV.mARG->outED ) )
									{
										ENV.appendOutput_wrtAEES( tmpED );
									}
								}
								prevRTC.splice( nextRTC );
							}
							else if( tmpED != ENV.mARG->outED )
							{
								ENV.appendOutput_wrtAEES( tmpED );
							}
						}
						else
						{
							return( false );
						}

						break;
					}

					case AEES_STMNT_BREAK:
					case AEES_STMNT_RETURN:
					{
						ENV.outEDS.append( tmpED );
						break;
					}

					default:
					{
						ENV.destroyOutED();

						AVM_OS_FATAL_ERROR_EXIT
								<< "Unexpected ENDIND EXECUTION STATUS :> "
								<< RuntimeDef::strAEES( tmpED->mAEES ) << " !!!"
								<< SEND_EXIT;

						return( false );
					}
				}
			}
		}
		else if( not ENV.appendOutput_mwsetPES(ENV.mARG->outED, rtcRID,
				PROCESS_RUNNING_STATE) )
		{
			return( true );
		}

		// Sync EDS traitement
		ENV.spliceSync_mwStorePos(tmpENV);

		// IRQ EDS traitement
		ENV.spliceNotOutput(tmpENV);
	}
	else
	{
		if( not ENV.mARG->outED->hasRunnableElementTrace() )
//		if( ENV.mARG->outED->isCreated( tmpRID ) )
		{
			ENV.mARG->outED->mAEES = AEES_STMNT_NOTHING;
		}

		ENV.outEDS.append( ENV.mARG->outED );
	}

	return( true );
}


bool AvmPrimitive_Rtc::resume(ExecutionEnvironment & ENV)
{
	ENV.outEDS.append( ENV.inED );

	return( true );
}


/**
 ***************************************************************************
 * execution of a SCHEDULE#INVOKE program
 ***************************************************************************
 */
bool AvmPrimitive_ScheduleInvoke::run(ExecutionEnvironment & ENV)
{
	ENV.mARG->outED->mRID = ENV.mARG->at(0).bfRID();

	if( ENV.mARG->outED->isunRunnable( ENV.mARG->outED->mRID ) )
	{
		return( true );
	}
	else
	{
		const BFCode & onInvoke = ENV.mARG->outED->getRuntimeFormOnSchedule(
				ENV.mARG->outED->mRID);

		if( onInvoke.valid() &&
				ENV.mARG->outED->isRunnable( ENV.mARG->outED->mRID ) )
		{
			ExecutionEnvironment tmpENV(ENV, ENV.mARG->outED, onInvoke);
			if( tmpENV.run(PROCESS_RUNNING_STATE) )
			{
				ENV.spliceOutput(tmpENV);
			}
			else
			{
				return( false );
			}
		}
		else
		{
			if( not ENV.mARG->outED->hasRunnableElementTrace() )
//			if( ENV.mARG->outED->isCreated( tmpRID ) )
			{
				ENV.mARG->outED->mAEES = AEES_STMNT_NOTHING;
			}

			ENV.outEDS.append( ENV.mARG->outED );
		}
	}

	return( true );
}


/**
 ***************************************************************************
 * execution of a SCHEDULE#GET program
 ***************************************************************************
 */
bool AvmPrimitive_ScheduleGet::seval(EvaluationEnvironment & ENV)
{
	ENV.outVAL = ENV.mARG->outED->getRuntimeFormOnSchedule(ENV.mARG->at(0).bfRID());

	return( true );
}


/**
 ***************************************************************************
 * execution of a SCHEDULE#IN program
 ***************************************************************************
 */
bool AvmPrimitive_ScheduleIn::seval(EvaluationEnvironment & ENV)
{
	const BFCode & scheduleCode = ENV.mARG->outED->getRuntimeFormOnSchedule(
			ENV.mARG->at(1).bfRID() );

	const RuntimeID & aRID = ENV.mARG->at(0).bfRID();

	if( scheduleCode.valid() && aRID.valid() )
	{
		ENV.outVAL = ExpressionConstructor::newBoolean(
				StatementFactory::containsOperationOnRID(
						scheduleCode, AVM_OPCODE_RUN, aRID));

		return( true );
	}

	return( false );
}


/**
 ***************************************************************************
 * execution of a SCHEDULE#SET program
 ***************************************************************************
 */
bool AvmPrimitive_ScheduleSet::run(ExecutionEnvironment & ENV)
{
	ENV.mARG->outED.mwsetRuntimeFormOnSchedule(
			ENV.mARG->at(0).bfRID(), ENV.mARG->at(1).bfCode());

	ENV.outEDS.append( ENV.mARG->outED );

	return( true );
}



/**
 ***************************************************************************
 * execution of a DEFER#INVOKE program
 ***************************************************************************
 */
bool AvmPrimitive_DeferInvoke::run(ExecutionEnvironment & ENV)
{
	const RuntimeID & deferRID = ENV.mARG->at(0).bfRID();

	if( ENV.mARG->outED->isunRunnable( deferRID ) )
	{
		return( true );
	}
	else
	{
		const BFCode & aRunCode = ENV.mARG->outED->getRuntimeFormOnDefer(deferRID);

		if( aRunCode.valid() && ENV.mARG->outED->isRunnable( deferRID ) )
		{
			BFCode aRunCode = ENV.mARG->outED->getRuntimeFormOnDefer(deferRID);

			ExecutionEnvironment tmpENV(ENV, ENV.mARG->outED, deferRID, aRunCode);
			if( tmpENV.run(PROCESS_RUNNING_STATE) )
			{
				ENV.spliceOutput(tmpENV);
			}
			else
			{
				return( false );
			}
		}
		else
		{
			ENV.outEDS.append( ENV.inED );
		}
	}

	return( true );
}


/**
 ***************************************************************************
 * execution of a DEFER#GET program
 ***************************************************************************
 */
bool AvmPrimitive_DeferGet::seval(EvaluationEnvironment & ENV)
{
	ENV.outVAL = ENV.mARG->outED->getRuntimeFormOnDefer(ENV.mARG->at(0).bfRID());

	return( true );
}


/**
 ***************************************************************************
 * execution of a DEFER#SET program
 ***************************************************************************
 */
bool AvmPrimitive_DeferSet::run(ExecutionEnvironment & ENV)
{
	ENV.mARG->outED.mwsetRuntimeFormOnDefer(
			ENV.mARG->at(0).bfRID(), ENV.mARG->at(1).bfCode());

	ENV.outEDS.append( ENV.mARG->outED );

	return( true );
}




/**
 ***************************************************************************
 * execution of a FORK program
 ***************************************************************************
 */
bool AvmPrimitive_Fork::run(ExecutionEnvironment & ENV)
{
	AvmCode::const_iterator it = ENV.inCODE->begin();
	AvmCode::const_iterator endIt = ENV.inCODE->end();
	for( ; it != endIt ; ++it )
	{
		ENV.run( *it );
	}

	return( true );
}


/**
 ***************************************************************************
 * execution of a JOIN program
 ***************************************************************************
 */

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// CHECK MOC
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmPrimitive_Join::checksatJoin(
		ExecutionEnvironment & ENV, const BF & aJoinSpec)
{
	switch( aJoinSpec.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			const BFCode & aCode = aJoinSpec.bfCode();

			switch ( aCode->getAvmOpCode() )
			{
				case AVM_OPCODE_NOT:
				{
					return( not checksatJoin(ENV, aCode->first()) );
				}

				case AVM_OPCODE_AND:
				case AVM_OPCODE_STRONG_SYNCHRONOUS:
				{
					AvmCode::iterator itForm = aCode->begin();
					AvmCode::iterator endForm = aCode->end();
					for( ; itForm != endForm ; ++itForm )
					{
						if( not checksatJoin(ENV, *itForm) )
						{
							return( false );
						}
					}
					return( true );
				}

				case AVM_OPCODE_OR:
				case AVM_OPCODE_WEAK_SYNCHRONOUS:
				{
					AvmCode::iterator itForm = aCode->begin();
					AvmCode::iterator endForm = aCode->end();
					for( ; itForm != endForm ; ++itForm )
					{
						if( checksatJoin(ENV, *itForm) )
						{
							return( true );
						}
					}
					return( false );
				}

				case AVM_OPCODE_XOR:
				case AVM_OPCODE_EXCLUSIVE:
				{
					avm_size_t nbTrue = 0;

					AvmCode::iterator itForm = aCode->begin();
					AvmCode::iterator endForm = aCode->end();
					for( ; itForm != endForm ; ++itForm )
					{
						if( checksatJoin(ENV, *itForm) )
						{
							++nbTrue;
						}
					}
					return( nbTrue == 1 );
				}

				default:
				{
					return( false );
				}
			}
			return( false );
		}

		case FORM_RUNTIME_ID_KIND:
		{
			return( ENV.inED->isWaitingJoin( aJoinSpec.bfRID() ) );
		}

		case FORM_INSTANCE_MACHINE_KIND:
		case FORM_INSTANCE_DATA_KIND:
		{
			//return( ENV.inED->isWaitingJoin( ENV.evalMachine(aJoinSpec) ) );
			return( false );
		}

		default:
		{
			return( false );
		}
	}
}


bool AvmPrimitive_Join::run(ExecutionEnvironment & ENV)
{
	APExecutionData outED = ENV.inED;
	outED.mwsetAEES( AEES_WAITING_JOIN_FORK );

	if( tableOfWaitingJoin.empty() )
	{
		tableOfWaitingJoin.resize( ENV.inED->getTableOfRuntime().size() );

		outED.mwsetRuntimeFormState(outED->mRID, PROCESS_WAITING_JOIN_STATE);
		tableOfWaitingJoin[ outED->mRID.getOffset() ].append( outED );
	}
	else if( tableOfWaitingJoin[ outED->mRID.getOffset() ].empty() )
	{
		outED.mwsetRuntimeFormState(outED->mRID, PROCESS_WAITING_JOIN_STATE);
		tableOfWaitingJoin[ outED->mRID.getOffset() ].append( outED );
	}

	else if( tableOfWaitingJoin[ outED->mRID.getOffset() ].singleton() )
	{
		const APExecutionData & otherED =
				tableOfWaitingJoin[ outED->mRID.getOffset() ].first();

		APExecutionData joinED = AvmSynchronizationFactory::fusion(
				outED->getExecutionContext()->LCA(
					otherED->getExecutionContext())->getAPExecutionData(),
				outED, otherED );
		if( joinED.valid() )
		{
			joinED->setRuntimeFormState(outED->mRID, PROCESS_IDLE_STATE);
			joinED.mwsetAEES( AEES_OK );
			ENV.outEDS.append( joinED );

			tableOfWaitingJoin[ outED->mRID.getOffset() ].clear();
		}
	}
	else if( tableOfWaitingJoin[ outED->mRID.getOffset() ].populated() )
	{
		APExecutionData joinED = outED;

		ListOfAPExecutionData::const_iterator itED =
				tableOfWaitingJoin[ outED->mRID.getOffset() ].begin();
		ListOfAPExecutionData::const_iterator endED =
				tableOfWaitingJoin[ outED->mRID.getOffset() ].end();
		for( ; itED != endED ; ++itED )
		{
			joinED = AvmSynchronizationFactory::fusion(
					outED->getExecutionContext()->LCA(
						(*itED)->getExecutionContext())->getAPExecutionData(),
					joinED, *itED);
			if( joinED.invalid() )
			{
				break;
			}
			joinED->setRuntimeFormState(outED->mRID, PROCESS_IDLE_STATE);
		}

		if( joinED.valid() )
		{
			joinED.mwsetAEES( AEES_OK );
			ENV.outEDS.append( joinED );

			tableOfWaitingJoin[ outED->mRID.getOffset() ].clear();
		}
	}

	return( true );
}


/**
 ***************************************************************************
 * execution of a RDV program
 ***************************************************************************
 */
bool AvmPrimitive_Rdv::run(ExecutionEnvironment & ENV)
{
//	const RuntimeID & tmpRID = ENV.mARG->at(0).bfRID();

//	ENV.outEDS.append( ENV.mARG->outED );

	return( true );
}



}
