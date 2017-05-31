/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 26 juil. 2008
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/
#include "BaseCoverageFilter.h"

#include <fam/queue/ExecutionQueue.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <sew/Configuration.h>
#include <sew/Workflow.h>


#include <boost/format.hpp>


namespace sep
{


/**
 *******************************************************************************
prototype filter::machine_coverage as &avm::core.filter.MACHINE_COVERAGE is
	section PROPERTY
		// Nombre de pas de calcul "cumulés" avant de débuter la vérification de la couverture
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

		// choix de l'heuristique de départ
		// basic | naive | smart | agressive
		@heuristic#start = 'basic';

		// Nombre d'essais d'heuristiques
		@heuristic#trials = 7;

		// Critère de satisfaction du succès des heuristiques
		// taux de couverte / nombre d'élément restant...
		@objective#rate = 95;
		@objective#rest = 5;
	endsection PROPERTY

	section LOG
		// %1% --> number of Covered Elements
		// %2% --> number of Elements
		@eval   = "coverage: %1% / %2%\n";
		@result = "coverage: %1% / %2%\n";
		@report = "coverage: %1% / %2%\n";
	endsection LOG
endprototype
 *******************************************************************************
 */

/**
 * CONFIGURE
 */
bool BaseCoverageFilter::configureImpl()
{
	mCoverageStatistics.resetCounter();

	long intProperty = 0;

	// Global config scope
	WObject * sectionSYMBEX = getConfiguration().getWorkflow().getSYMBEX();

	mBackwardAnalysisLookaheadDepth =
			Query::getRegexWPropertySizeT( sectionSYMBEX, OR_WID2(
					CONS_WID4("backward", "analysis", "lookahead", "depth"),
					CONS_WID3("backward", "depth", "analyze") ), // @Deprecated
				AVM_NUMERIC_MAX_SIZE_T, AVM_NUMERIC_MAX_SIZE_T);

	mForwardAnalysisLookaheadDepth =
			Query::getRegexWPropertySizeT( sectionSYMBEX,
					CONS_WID4("forward", "analysis", "lookahead", "depth"),
				AVM_NUMERIC_MAX_SIZE_T, AVM_NUMERIC_MAX_SIZE_T);


	WObject * thePROPERTY = Query::getRegexWSequence(
			getParameterWObject(), OR_WID2("property", "PROPERTY"));

	if( thePROPERTY != WObject::_NULL_ )
	{
		intProperty = Query::getRegexWPropertyInt(
				thePROPERTY, CONS_WID2("(start|begin)", "step"), 0);
		if( intProperty < 0 )
		{
			AVM_OS_LOG << "Invalid eval begining step ! => replace by << "
					<< 1 << " >>" << std::endl;

			mBeginningStepTimout = 0;
		}
		else
		{
			mBeginningStepTimout = intProperty;
		}

		mStopFlag  = Query::getWPropertyBoolean(thePROPERTY, "stop", false);

		mMinimizationFlag =
				Query::getWPropertyBoolean(thePROPERTY, "minimize", true);

		mNormalizationFlag =
				Query::getWPropertyBoolean(thePROPERTY, "normalize", true);

		mBreakFlag = Query::getWPropertyBoolean(thePROPERTY, "break", false);

		mSliceFlag = Query::getWPropertyBoolean(thePROPERTY, "slice", false);
	}


	mConfigFlag = mHeuristicProperty.configure( getParameterWObject() )
			&& mConfigFlag;

	WObject * theHEURISTIC = Query::getRegexWSequence(getParameterWObject(),
			OR_WID2("heuristic", "HEURISTIC"), thePROPERTY);
	if( (theHEURISTIC != WObject::_NULL_) /*&& mHeuristicFlag*/ )
	{
		mHeuristicProperty.mHeuristicClass =
				AvmCoverageHeuristicProperty::toHeuristicClass(
						Query::getRegexWPropertyString(theHEURISTIC,
								CONS_WID2("heuristic", "start"), "basic") );

		intProperty = Query::getRegexWPropertyInt(
				theHEURISTIC, CONS_WID2("objective", "rate"), 100);
		mCoverageStatistics.mCoverageRateGoal = ( (intProperty > 0) &&
				(intProperty <= 100) ) ?  intProperty : 100;

		mCoverageStatistics.mCoverageRestGoal =
				Query::getRegexWPropertySizeT(
						theHEURISTIC, CONS_WID2("objective", "rest"), 0, 0);

		// Local config scope
		mBackwardAnalysisLookaheadDepth = Query::getRegexWPropertySizeT(
			theHEURISTIC, OR_WID2(
				CONS_WID4("backward", "analysis", "lookahead", "depth"),
				CONS_WID3("backward", "depth", "analyze") ), // @Deprecated
			mBackwardAnalysisLookaheadDepth,
			mBackwardAnalysisLookaheadDepth);

		mForwardAnalysisLookaheadDepth = Query::getRegexWPropertySizeT(
			theHEURISTIC, CONS_WID4("forward", "analysis", "lookahead", "depth"),
			mForwardAnalysisLookaheadDepth, mForwardAnalysisLookaheadDepth);
	}

	return true;
}


/**
 * PRE-PROCESS
 */
bool BaseCoverageFilter::preprocess()
{
	if( mHeuristicProperty.mHeuristicEnabled )
	{
		if( not mStatemachineReachability.computeReachableComponent(
				getConfiguration(), mBackwardAnalysisLookaheadDepth) )
		{
			return( false );
		}

AVM_IF_DEBUG_FLAG2( PRE_PROCESSING , EXECUTABLE )
	getConfiguration().serializeDebugExecutable( "preprocess" );
AVM_ENDIF_DEBUG_FLAG2( PRE_PROCESSING , EXECUTABLE )
	}

	return( true );
}


/**
 * PRE-FILTER
 */
bool BaseCoverageFilter::prefilter()
{
	if( mCoverageStatistics.goalAchieved() && mStopFlag )
	{
		ecQueue = &( getExecutionQueue().getReadyQueue() );

		ExecutionContext * anEC = NULL;
		while( ecQueue->nonempty() )
		{
			ecQueue->pop_first_to( anEC );

			getExecutionQueue().appendFailed( anEC );
		}

		return false;
	}

	return true;
}


/**
 * FILTERING FINALIZE
 */
bool BaseCoverageFilter::filteringFinalize()
{
	if( mSliceFlag )
	{
		mListOfLeafEC.clear();

		// ELAGAGE DANS TOUT LE GRAPH!!!!!
		computeLeafEC(getConfiguration().getTrace(), mListOfLeafEC);

		slice(mListOfLeafEC);
	}

	return( true );
}


////////////////////////////////////////////////////////////////////////////////
// FINAL SLICING TOOLS
////////////////////////////////////////////////////////////////////////////////

bool BaseCoverageFilter::isSliceableContext(ExecutionContext & anEC) const
{
	if( mListOfPositiveEC.contains(& anEC)  )
	{
		return( false );
	}
	else
	{
		return( AbstractProcessorUnit::isSliceableContext(anEC) );
	}
}


/**
 * GOAL_ACHIEVED
 */
void BaseCoverageFilter::handleRequestGoalAchieved()
{
	//!! NOTHING
}

/**
 * EVAL TRACE
 */
void BaseCoverageFilter::traceMinimumPreEval(
		OutStream & os, const ExecutionContext & anEC) const
{
	boost::format formatter(mPreEvalTraceFormatter);
	formatter.exceptions( boost::io::no_error_bits );

//	formatter.exceptions( boost::io::all_error_bits ^
//			( boost::io::too_many_args_bit | boost::io::too_few_args_bit ) );

	os << formatter
			% mCoverageStatistics.mNumberOfCovered
			% mCoverageStatistics.mNumberOfElements
			<< std::flush;
}


void BaseCoverageFilter::traceDefaultPreEval(
		OutStream & os, const ExecutionContext & anEC) const
{
	os << "coverage< " << getParameterWObject()->getNameID() << " >: "
			<< mCoverageStatistics.mNumberOfCovered << " / "
			<< mCoverageStatistics.mNumberOfElements << std::endl;
}


void BaseCoverageFilter::traceBoundEval(OutStream & os) const
{
	boost::format formatter(mBoundEvalTraceFormatter);
	formatter.exceptions( boost::io::no_error_bits );

//	formatter.exceptions( boost::io::all_error_bits ^
//			( boost::io::too_many_args_bit | boost::io::too_few_args_bit ) );

	os << formatter
			% mCoverageStatistics.mNumberOfCovered
			% mCoverageStatistics.mNumberOfElements
			<< std::flush;
}


void BaseCoverageFilter::reportEval(OutStream & os) const
{
	boost::format formatter(mReportEvalTraceFormatter);
	formatter.exceptions( boost::io::no_error_bits );

//	formatter.exceptions( boost::io::all_error_bits ^
//			( boost::io::too_many_args_bit | boost::io::too_few_args_bit ) );

	os << formatter
			% mCoverageStatistics.mNumberOfCovered
			% mCoverageStatistics.mNumberOfElements
			<< std::flush;
}



}
