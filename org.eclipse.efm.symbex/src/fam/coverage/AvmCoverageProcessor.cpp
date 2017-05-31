/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 19 nov. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmCoverageProcessor.h"

#include <fam/queue/ExecutionQueue.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <sew/SymbexControllerRequestManager.h>


namespace sep
{


/*
prototype processor::coverage "coverage processor" as avm::processor.COVERAGE is
	section PROPERTY
		// Nombre de pas de calcul "cumulés" avant de débuter
		// la vérification de la couverture
		@begin_step = 0;

		// Arrète l'exécution dès que la couverture est complète
		@stop = true;

		// Arrète l'exécution au plutôt
		@minimize = true;

		// Arrète l'exécution du chemin courant dès qu'un objectif est atteint
		@break = true;

		// Elagage du graphe des scénarios à la fin de la vérification
		@slice = true;

		// Active l'utilisation d'heuristique
		@heuristic = true;

		@scope = 'DETAILS'; 	// 'INSTANCE' | 'FORM' | 'DETAILS'
	endsection PROPERTY


	// Utilisé pour préciser les machines ou les transitions particulières à couvrir!
	section DETAILS
		@form = spec::ascenseur.ascenseur.controler;
		@instance = spec::ascenseur.ascenseur.enregistrer;

		@transition = spec::ascenseur.ascenseur.aller_a_l_etage.attente.transition#6;
	endsection DETAILS


	section HEURISTIC
		// choix de l'heuristique de départ
		// basic | naive | smart | agressive
		@heuristic#start = 'basic';

		// Nombre d'essais d'heuristiques
		@heuristic#trials = 7;

		// Critère de satisfaction du succès des heuristiques
		// taux de couverte / nombre d'élément restant...
		@objective#rate = 95;
		@objective#rest = 5;


		// Choix des contextes avec des transitions
		// [ fortement | faiblement | autre ] tirables

		// Limitations temporaire de la profondeur d'exploration
		@coverage#height = 7;

		// nombre de fois que la limite doit être atteint avant de l'augmenter
		@coverage#height#reached#limit = 42;

		@hit#strongly#random = false;
		@hit#strongly#count = 1;

		@hit#weakly#random = false;
		@hit#weakly#count = 1;

		@hit#other#random = false;
		@hit#other#count = 1;
	endsection HEURISTIC
endprototype
*/


////////////////////////////////////////////////////////////////////////////////
// CONFIGURE API
////////////////////////////////////////////////////////////////////////////////

bool AvmCoverageProcessor::configureImpl()
{
	// SUPER CONFIGURATION
	mConfigFlag = BaseCoverageFilter::configureImpl();

	WObject * thePROPERTY = Query::getRegexWSequence(
			getParameterWObject(), OR_WID2("property", "PROPERTY"));

	if( thePROPERTY != WObject::_NULL_ )
	{
		mScope = Specifier::toDesignKind(
				Query::getWPropertyString(thePROPERTY, "scope", "MODEL") );
	}

	mConfigFlag = mHeuristicProperty.configure( getParameterWObject() )
			&& mConfigFlag;

	mConfigFlag = mTransitionCoverage.configure()
			&& mConfigFlag;

	mConfigFlag = mOneTraceDriver.configure()
			&& mConfigFlag;

	enablePreprocess( this );

	return mConfigFlag;
}


////////////////////////////////////////////////////////////////////////////////
// REPORT API
////////////////////////////////////////////////////////////////////////////////

void AvmCoverageProcessor::reportMinimum(OutStream & os) const
{
	os << TAB << "COVERAGE PROCESSOR" << EOL_FLUSH;

	mTransitionCoverage.reportMinimum(os);

	////////////////////////////////////////////////////////////////////////////
	// SET EXIT CODE
	mCoverageStatistics.setExitCode();
}

void AvmCoverageProcessor::reportDefault(OutStream & os) const
{
	reportHeader(os, "TRANSITION COVERAGE ");

	mTransitionCoverage.reportDefault(os);

	////////////////////////////////////////////////////////////////////////////
	// SET EXIT CODE
	mCoverageStatistics.setExitCode();
}



////////////////////////////////////////////////////////////////////////////////
// PROCESS API
////////////////////////////////////////////////////////////////////////////////

bool AvmCoverageProcessor::preprocess()
{
	return( BaseCoverageFilter::preprocess() );
}


bool AvmCoverageProcessor::postprocess()
{
	return( BaseCoverageFilter::postprocess() );
}


////////////////////////////////////////////////////////////////////////////////
// PRE-FILTER API
////////////////////////////////////////////////////////////////////////////////

bool AvmCoverageProcessor::prefilter()
{
	ecQueue = &( getExecutionQueue().getReadyQueue() );

//	ecQueueIt = ecQueue->begin();
//	ecQueueItEnd = ecQueue->end();
//	for( ; ecQueueIt != ecQueueItEnd ; ++ecQueueIt )
//	{
//		prefilter(*ecQueueIt);
//	}

	if( mCoverageStatistics.goalAchieved() && mStopFlag )
	{
		getSymbexRequestManager().postRequestStop( this );

		return false;
	}

	switch( mHeuristicProperty.mHeuristicClass )
	{
		// SMART PASSIVE TRANSITION COVERAGE HEURISTIC
		// Using :> HIGH PRIORITY CONTEXT
		// w.r.t. TRANSITION FIREABILITY
		case IHeuristicClass::HEURISTIC_BASIC_CLASS:
		{
			return( mTransitionCoverage.prefiltering(*ecQueue) );
		}

		// SMART ACTIVE TRANSITION COVERAGE HEURISTIC
		// Using :> ONE TRACE DRIVEN
		case IHeuristicClass::HEURISTIC_NAIVE_CLASS:
		{
			return( mOneTraceDriver.prefiltering(*ecQueue) );
		}

		// SMART ACTIVE TRANSITION COVERAGE HEURISTIC
		// Using :> MANY TRACE DRIVEN
		case IHeuristicClass::HEURISTIC_SMART_CLASS:
		{
			return( mManyTraceDriver.prefiltering(*ecQueue) );
		}


		case IHeuristicClass::HEURISTIC_AGRESSIVE_CLASS:

		// SMART PASSIVE TRANSITION COVERAGE HEURISTIC
		// Using :> PRIORITY CONTEXT
		// w.r.t. TRANSITION FIREABILITY
		case IHeuristicClass::HEURISTIC_NOTHING_ELSE_CLASS:
		default:
		{
			return( mTransitionCoverage.prefiltering(*ecQueue) );
		}
	}

	return( getExecutionQueue().hasReady() );
}


////////////////////////////////////////////////////////////////////////////////
// POST-FILTER API
////////////////////////////////////////////////////////////////////////////////

bool AvmCoverageProcessor::postfilter()
{
	ecQueue = &( getExecutionQueue().getResultQueue() );

	if( mCoverageStatistics.hasUncovered() )
	{
		mCoverageStatistics.backupCovered();

		if( mTransitionCoverage.postfiltering(*ecQueue) )
		{
			if( mCoverageStatistics.goalAchieved() )
			{
				getSymbexRequestManager().postRequestGoalAchieved( this );

				return( getExecutionQueue().hasResult() );
			}
		}


		// Coverage without heuristic usage !!!
		if( not mHeuristicProperty.mHeuristicEnabled )
		{
			return( getExecutionQueue().hasResult() );
		}


		if( mCoverageStatistics.updateFailedStep() )
		{
			//!!! TODO optimization decision
			if( mCoverageStatistics.isSeriouslyFailedStep() )
			{
//				incrHeuristicClass();

				getSymbexRequestManager().postRequestRequeueWaiting( this );


AVM_IF_DEBUG_FLAG( PROCESSOR )
	AVM_OS_COUT  << EMPHASIS(mHeuristicProperty.strHeuristicClass(), '*', 80);
	AVM_OS_TRACE << EMPHASIS(mHeuristicProperty.strHeuristicClass(), '*', 80);
AVM_ENDIF_DEBUG_FLAG( PROCESSOR )
				}

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	mCoverageStatistics.toStreamFailedStep(AVM_OS_COUT,
			"No new transition covered since << ", " step", " >> !!!\n");
	mCoverageStatistics.toStreamFailedStep(AVM_OS_TRACE,
			"No new transition covered since << ", " step", " >> !!!\n");
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
		}
		else
		{
			mCoverageStatistics.resetFailedStep();
		}

		disableRequestStatus();

AVM_IF_DEBUG_FLAG( PROCESSOR )
	AVM_OS_COUT  << EMPHASIS("postfilter :> " +
			mHeuristicProperty.strHeuristicClass(), '*', 80);
	AVM_OS_TRACE << EMPHASIS("postfilter :> " +
			mHeuristicProperty.strHeuristicClass(), '*', 80);
AVM_ENDIF_DEBUG_FLAG( PROCESSOR )

		switch( mHeuristicProperty.mHeuristicClass )
		{
			// SMART PASSIVE TRANSITION COVERAGE HEURISTIC
			// Using :> HIGH PRIORITY CONTEXT
			// w.r.t. TRANSITION FIREABILITY
			case IHeuristicClass::HEURISTIC_BASIC_CLASS:
			{
				if( mTransitionCoverage.computeHighPriorityContext(
					(*ecQueue), getExecutionQueue().refWaitingStrategy()) )
				{
					//!! NOTHING
				}

				//!! FAILED CASE
				else if( isRequestStatus( REQUEST_REQUEUE_WAITING_STATUS ) )
				{
					getSymbexRequestManager().postRequestRequeueWaiting( this );
				}

				// Require changing heuristic
				else if( isRequestStatus( REQUEST_HEURISTIC_STATUS ) )
				{
					mHeuristicProperty.mHeuristicClass =
							IHeuristicClass::HEURISTIC_NAIVE_CLASS;

					getSymbexRequestManager().postRequestRequeueWaiting( this );
				}

				break;
			}

			// SMART ACTIVE TRANSITION COVERAGE HEURISTIC
			// Using :> ONE TRACE DRIVEN
			case IHeuristicClass::HEURISTIC_NAIVE_CLASS:
			{
				if( mOneTraceDriver.postfiltering(*ecQueue) )
				{
					if( mOneTraceDriver.goalAchieved() )
					{
						if( mCoverageStatistics.isSuccessfulStep() ||
							getExecutionQueue().getWaitingStrategy()->
									hasWaiting(WEIGHT_STRONGLY_ACHIEVABLE) )
						{
							mHeuristicProperty.mHeuristicClass =
									IHeuristicClass::HEURISTIC_BASIC_CLASS;
						}

						getSymbexRequestManager().postRequestRequeueWaiting( this );
					}
				}

				//!! FAILED CASE
				else if( isRequestStatus( REQUEST_REQUEUE_WAITING_STATUS ) )
				{
					if( mCoverageStatistics.isSuccessfulStep() ||
						getExecutionQueue().getWaitingStrategy()->
								hasWaiting(WEIGHT_STRONGLY_ACHIEVABLE) )
					{
						mHeuristicProperty.mHeuristicClass =
								IHeuristicClass::HEURISTIC_BASIC_CLASS;
					}

					getSymbexRequestManager().postRequestRequeueWaiting( this );
				}

				// Require changing heuristic
				else if( isRequestStatus( REQUEST_HEURISTIC_STATUS ) )
				{
					mHeuristicProperty.mHeuristicClass =
//							IHeuristicClass::HEURISTIC_SMART_CLASS;
							IHeuristicClass::HEURISTIC_NOTHING_ELSE_CLASS;

					getSymbexRequestManager().postRequestRequeueWaiting( this );
				}

				break;
			}

			// SMART ACTIVE TRANSITION COVERAGE HEURISTIC
			// Using :> MANY TRACE DRIVEN
			case IHeuristicClass::HEURISTIC_SMART_CLASS:
			{
				if( mManyTraceDriver.postfiltering(*ecQueue) )
				{
					//!! NOTHING
				}

				//!! FAILED CASE
				else if( isRequestStatus( REQUEST_REQUEUE_WAITING_STATUS ) )
				{
					getSymbexRequestManager().postRequestRequeueWaiting( this );
				}

				// Require changing heuristic
				else if( isRequestStatus( REQUEST_HEURISTIC_STATUS ) )
				{
					mHeuristicProperty.mHeuristicClass =
							IHeuristicClass::HEURISTIC_AGRESSIVE_CLASS;

					getSymbexRequestManager().postRequestRequeueWaiting( this );
				}

				break;
			}


			case IHeuristicClass::HEURISTIC_AGRESSIVE_CLASS:

			// SMART PASSIVE TRANSITION COVERAGE HEURISTIC
			// Using :> PRIORITY CONTEXT
			// w.r.t. TRANSITION FIREABILITY
			case IHeuristicClass::HEURISTIC_NOTHING_ELSE_CLASS:
			default:
			{
				if( mTransitionCoverage.computePriorityContext(
					(*ecQueue), getExecutionQueue().refWaitingStrategy()) )
				{
					if( mCoverageStatistics.isSuccessfulStep() ||
						getExecutionQueue().getWaitingStrategy()->
								hasWaiting(WEIGHT_STRONGLY_ACHIEVABLE) )
					{
						mHeuristicProperty.mHeuristicClass =
								IHeuristicClass::HEURISTIC_BASIC_CLASS;
					}
				}

				//!! FAILED CASE
				else if( isRequestStatus( REQUEST_REQUEUE_WAITING_STATUS ) )
				{
					getSymbexRequestManager().postRequestRequeueWaiting( this );
				}

				// Require changing heuristic
				else if( isRequestStatus( REQUEST_HEURISTIC_STATUS ) )
				{
					if( mCoverageStatistics.isSuccessfulStep() ||
						getExecutionQueue().getWaitingStrategy()->
								hasWaiting(WEIGHT_STRONGLY_ACHIEVABLE) )
					{
						mHeuristicProperty.mHeuristicClass =
								IHeuristicClass::HEURISTIC_BASIC_CLASS;
					}
				}

				break;
			}
		}
	}

	return( getExecutionQueue().hasResult() );
}


////////////////////////////////////////////////////////////////////////////////
// PROCESSOR REQUEST API
////////////////////////////////////////////////////////////////////////////////
/**
 * STOP  | RELEASE
 * RESET | RESTART | CONTINUE
 * REQUEUE_WAITING | REQUEUE_RESERVE
 * HEURISTIC | GOAL_ACHIEVED
 */
void AvmCoverageProcessor::handleRequestRequeueWaitingTable(
		WaitingStrategy & aWaitingStrategy,
		avm_uint8_t aWeightMin, avm_uint8_t aWeightMax)
{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , QUEUE )
	AVM_OS_TRACE << "AvmCoverageProcessor::handleRequestRequeueWaitingTable :>"
			<< std::endl;
	aWaitingStrategy.toStream(AVM_OS_TRACE);
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , QUEUE )


	while( true )
	{
		disableRequestStatus();

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_COUT  << EMPHASIS("requeue :> " +
			mHeuristicProperty.strHeuristicClass(), '*', 80);
	AVM_OS_TRACE << EMPHASIS("requeue :> " +
			mHeuristicProperty.strHeuristicClass(), '*', 80);
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )

		switch( mHeuristicProperty.mHeuristicClass )
		{
			case IHeuristicClass::HEURISTIC_BASIC_CLASS:
			{
				if( mTransitionCoverage.highRequeueWaitingTable(
						aWaitingStrategy, aWeightMin, aWeightMax) )
				{
					return;
				}

				//!! FAILED CASE
				else if( isRequestStatus( REQUEST_REQUEUE_WAITING_STATUS ) )
				{
					return;
				}

				// Require changing heuristic
				else if( isRequestStatus( REQUEST_HEURISTIC_STATUS ) )
				{
					mHeuristicProperty.mHeuristicClass =
							IHeuristicClass::HEURISTIC_NAIVE_CLASS;

					//!! CONTINUE
				}
				else
				{
					return;
				}

				break;
			}

			case IHeuristicClass::HEURISTIC_NAIVE_CLASS:
			{
				if( mOneTraceDriver.requeueWaitingTable(
						aWaitingStrategy, aWeightMin, aWeightMax) )
				{
					return;
				}

				//!! FAILED CASE
				else if( isRequestStatus( REQUEST_REQUEUE_WAITING_STATUS ) )
				{
					mHeuristicProperty.mHeuristicClass =
							IHeuristicClass::HEURISTIC_NOTHING_ELSE_CLASS;

					//!! CONTINUE
				}

				// Require changing heuristic
				else if( isRequestStatus( REQUEST_HEURISTIC_STATUS ) )
				{
					mHeuristicProperty.mHeuristicClass =
//							IHeuristicClass::HEURISTIC_SMART_CLASS;
							IHeuristicClass::HEURISTIC_NOTHING_ELSE_CLASS;

					//!! CONTINUE
				}
				else
				{
					return;
				}

				break;
			}
			case IHeuristicClass::HEURISTIC_SMART_CLASS:
			{
				if( mManyTraceDriver.requeueWaitingTable(
						aWaitingStrategy, aWeightMin, aWeightMax) )
				{
					return;
				}

				//!! FAILED CASE
				else if( isRequestStatus( REQUEST_REQUEUE_WAITING_STATUS ) )
				{
					return;
				}

				// Require changing heuristic
				else if( isRequestStatus( REQUEST_HEURISTIC_STATUS ) )
				{
					mHeuristicProperty.mHeuristicClass =
							IHeuristicClass::HEURISTIC_AGRESSIVE_CLASS;

					//!! CONTINUE
				}
				else
				{
					return;
				}

				break;
			}


			case IHeuristicClass::HEURISTIC_AGRESSIVE_CLASS:

			case IHeuristicClass::HEURISTIC_NOTHING_ELSE_CLASS:
			default:
			{
				if( mTransitionCoverage.elseRequeueWaitingTable(
						aWaitingStrategy, aWeightMin, aWeightMax) )
				{
					return;
				}

				//!! FAILED CASE
				else if( isRequestStatus( REQUEST_REQUEUE_WAITING_STATUS ) )
				{
					return;
				}

				// Require changing heuristic
				else if( isRequestStatus( REQUEST_HEURISTIC_STATUS ) )
				{
					if( getExecutionQueue().getWaitingStrategy()->
							hasWaiting(WEIGHT_STRONGLY_ACHIEVABLE) )
					{
						mHeuristicProperty.mHeuristicClass =
								IHeuristicClass::HEURISTIC_BASIC_CLASS;
					}
					return;
				}
				else
				{
					return;
				}

				break;
			}
		}
	}
}


////////////////////////////////////////////////////////////////////////////////
// DEBUG PROCESSING API
////////////////////////////////////////////////////////////////////////////////

bool AvmCoverageProcessor::debugEvalCommandImpl()
{
	if( dbgDecodeCommand("-->") )
	{
		dbgCommandDirectiveTransition();

		return( true );
	}

	return( false );
}


void AvmCoverageProcessor::dbgCommandDirectiveTransition()
{
	dbgCommandTransition();

	AvmCoverageDirectiveTraceBuilder pathChecker(
			mDebugSelectedContext, mDebugSelectedTransition,
			IHeuristicClass::IHeuristicClass::HEURISTIC_SMART_CLASS, 64, 64);

	if( pathChecker.computePath() )
	{
		AVM_OS_COUT << "GOAL ACHIEVED !!!" << std::endl;
	}
	else
	{
		AVM_OS_COUT << "FAILED !!!" << std::endl;
	}

	AVM_OS_COUT << std::endl;

	pathChecker.report(AVM_OS_COUT);

	AVM_OS_COUT << std::flush;
}


} /* namespace sep */
