/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "SymbexController.h"

#include <fml/runtime/ExecutionContext.h>

#include <fam/queue/ExecutionQueue.h>

#include <main/SignalHandler.h>

#include <sew/SymbexControllerUnitManager.h>
#include <sew/SymbexDispatcher.h>


namespace sep
{

/**
 * CONSTRUCTOR
 * Default
 */
SymbexController::SymbexController(
		SymbexDispatcher & aSymbexDispatcher, WObject * wfParameterObject,
	SymbexControllerUnitManager & aControllerUnitManager)
: SymbexJob(aSymbexDispatcher, wfParameterObject, aControllerUnitManager),
mSymbexRequestManager( aSymbexDispatcher.getSymbexControllerRequestManager() )
{
	//!! NOTHING
}

/**
 * Thread main Run Method
 */
void SymbexController::operator()()
{
	AVM_OS_TRACE << "Begin SymbexController Thread" << std::endl;

	while( isLifecycleRunnable() )
	{
		analyseReady();

		analyseResult();
	}

	AVM_OS_TRACE << "End SymbexController Thread" << std::endl;
}


void SymbexController::analyseReady()
{
	RunnableElement::setLifecycleRunning();

	if( mSymbexDispatcher.hasWork() )
	{

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , REPORTING , COMPUTING )

AVM_IF_DEBUG_LEVEL_GTE_HIGH

	mControllerUnitManager.getExecutionQueue().toStream(AVM_OS_TRACE);

AVM_ELSEIF_DEBUG_LEVEL_GTE_MEDIUM

	mControllerUnitManager.getExecutionQueue().toStreamWaiting(AVM_OS_TRACE);

AVM_ENDIF_DEBUG_LEVEL_GTE_MEDIUM

	AVM_OS_TRACE << std::endl;

AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , REPORTING , COMPUTING )


		while( true )
		{

#ifdef __AVM_UNIX__

			if( SignalHandler::isSIGINT() )
			{
				mSymbexRequestManager.fireRequestStop();

				this->handleRequestStop();
			}

#endif /* __AVM_UNIX__ */

			/**
			 * PROCESSOR REQUEST API :> before << prefiltering >> step
			 * STOP | RELEASE | RESET | REQUEUE_WAITING
			 */
			if( mSymbexRequestManager.hasRequestStop() )
			{

AVM_IF_DEBUG_LEVEL_OR_FLAG( MEDIUM , COMPUTING )
	OSS oss( AVM_NO_INDENT );
	mSymbexRequestManager.strStopRequestor(oss, "");

	AVM_OS_INFO << std::endl << EMPHASIS(
			"STOP REQUIRED BY FILTERING PROCESSOR !!!", oss.str(), '*', 80);
AVM_ENDIF_DEBUG_LEVEL_OR_FLAG( MEDIUM , COMPUTING )


				mSymbexRequestManager.fireRequestStop();

				this->handleRequestStop();

				break;
			}

			if( mSymbexRequestManager.hasRequestRelease() )
			{
				mSymbexRequestManager.fireRequestRelease();

				this->handleRequestRelease();
			}

			if( mSymbexRequestManager.hasRequestReset() )
			{
				mSymbexRequestManager.fireRequestReset();

				this->handleRequestReset();
			}

			if( mSymbexRequestManager.hasRequestRequeueWaiting() )
			{
				mSymbexRequestManager.fireRequestRequeueWaiting();
			}


			/**
			 * PREFILTERING step
			 */
			// Si tout se passe bien on passera à la phase d'exécution symbolique
			if( mControllerUnitManager.prefilter() )
			{
				if( mControllerUnitManager.finalizePrefiltering() )
				{
					break;
				}
			}


			/**
			 * PROCESSOR REQUEST API :> check if has goal achieved
			 * GOAL_ACHIEVED
			 */
			if( mSymbexRequestManager.hasRequestGoalAchieved() )
			{
				mSymbexRequestManager.fireRequestGoalAchieved();

				this->handleRequestGoalAchieved();
			}

			// Sinon on repasse par la file d'attente pour récupérer de nouveaux
			// Execution Contextes attendant pour passer l'audition des pré-filtres
			if( mControllerUnitManager.getExecutionQueue().hasWaiting() )
			{
				mControllerUnitManager.getExecutionQueue().popWaiting2Ready();
			}

			/**
			 * PROCESSOR REQUEST API :> to continue if empty waiting queue
			 * CONTINUE | REQUEUE_RESERVE | RESTART
			 */
			// Si aucun candidat n'est disponible, alors on passe la main
			// aux filtres s'étant inscrits pour leur heuristique de
			// en phase de << finalize prefiltering >> !!!
			else if( mSymbexRequestManager.hasRequestsToContinue() )
			{
				if( mSymbexRequestManager.hasRequestContinue() )
				{
					mSymbexRequestManager.fireRequestContinue();
				}

				if( mSymbexRequestManager.hasRequestRequeueReserve() )
				{
					mSymbexRequestManager.fireRequestRequeueReserve();
				}

				if( mSymbexRequestManager.hasRequestRestart() )
				{
					mSymbexRequestManager.fireRequestRestart();
				}
			}

			// Autrement, il n'y a rien à faire !!!
			else
			{
				break;
			}
		}

		// Tous ceux qui ont passé l'audition des pré-filtres avec succès sont
		// mis en cache pour l'exécution symbolique
		if( mSymbexDispatcher.hasReadyWork() )
		{
			mSymbexDispatcher.getExecutionWorkingQueue().splice(
				mControllerUnitManager.getExecutionQueue().getReadyQueue());
		}
		else
		{
			this->handleRequestNoWork();
		}
	}
	else
	{
		handleRequestNoWork();
	}
}


void SymbexController::analyseResult()
{
	RunnableElement::setLifecycleRunning();

	if( this->hasSymbexContext() )
	{
		mControllerUnitManager.getExecutionQueue().
				spliceResult( this->getSymbexContexts() );

		if( mControllerUnitManager.postfilter() )
		{
			mControllerUnitManager.finalizePostfiltering();
		}

		/**
		 * PROCESSOR REQUEST API :> check if has goal achieved
		 * GOAL_ACHIEVED
		 */
		if( mSymbexRequestManager.hasRequestGoalAchieved() )
		{
			mSymbexRequestManager.fireRequestGoalAchieved();
		}
	}
	else
	{
//		RunnableElement::setLifecycleIdle();
		RunnableElement::setLifecycleSuspended();
	}
}


/**
 * report Eval
 */
void SymbexController::reportEval() const
{
	mControllerUnitManager.reportEval(AVM_OS_TRACE);

	mControllerUnitManager.reportEval(AVM_OS_COUT);
}


}
