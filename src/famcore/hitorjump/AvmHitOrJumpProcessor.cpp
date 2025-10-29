/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 7 janv. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmHitOrJumpProcessor.h"

#include "HitOrderedProcessor.h"
#include "HitUnorderedProcessor.h"

#include <collection/Typedef.h>

#include <fml/runtime/ExecutionContext.h>

#include <famcore/queue/ExecutionQueue.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <sew/SymbexControllerRequestManager.h>


namespace sep
{


/*
prototype process::hit_or_jump as &avm::processor.HIT_OR_JUMP is
 section REPORT
  @uri = std      ":" ( "cout" | "cerr"  )
       | avm      ":" ( "log"  | "trace" )
       | folder   ":" path
       | file     ":" path
       | filename ":" path
       | socket   ":" host ":" port
       ;
  @uri = ...;

  @when = [ init ][:][ otf | (every | after | before)?value#unit][:][ exit ] ;
 endsection REPORT

 section SCHEDULING
  @startup = 'waiting';
 endsection SCHEDULING

 section PROPERTY
  // Nombre de pas de calcul "cumulés" avant de débuter la vérification de la couverture
  @begin_step = 0;

  // Arrète l'exécution dès que la couverture est complète
  @stop = true;

  // Elagage du graphe des scénarios à la fin de la vérification
  @slice = true;

  // Active l'utilisation d'heuristique
  @heuristic = true;

  // Cherche une trace globalement ou locale à chaque noeud racine...
  @search#scope = 'GLOBALLY'; // GLOBALLY | LOCALLY ;

  // |;|     --> ordered     (operator: sequence)
  // |<|     --> ordered     (operator: order)
  // |i|     --> unordered   (operator: interleaving)
  // |regex| --> regex       (operator: regex)
  @scheduler = '|<|';


  // Hauteur du jump
  @jump#height = 4;

  // the Jump trials limit exploration property
  @jump#limit = 15;


  // Choisir des traces avec ou sans trous
  @hit#consecutive = false;

  // Rechercher un maximum de traces solutions
  // Possible backtracking
  @hit#max = false;

  // Ne faire qu'une tentative vers l'objectif (avoir de la chance!)
  // Pas de backtrack
  @hit#lucky = true;

  // Nombre de chemins positifs sélectionnables ALEATOIREMENT
  @hit#count  = -1;

  // Nombre de chemins négatifs sélectionnables ALEATOIREMENT
  @jump#count  = 1;

  // Effectue une sélection finale (relativement à @hit#count)
  // lorsque l'objectif est atteint !
  @hit#final  = true;

  // Slice les hit/jump non retenus aléatoirement
  @jump#slice  = true;
 endsection PROPERTY


 // Declaration part
 section POINT
  @assign = "sens";

  @newfresh = "sens";

  @signal#sens = "sens";

  @port = "env";

  @input = "env";
  @output = "env";

  @output = "Thermostat->dt";
  @input  = "Thermostat->equip";
  @output2 = "Equipment->error";
 endsection POINT

 section TRACE
  @trace = ${ && "signal#sens" "output2" };
  @trace = [ "signal#sens" , "output2" ];
  @point = ( "signal#sens" || "output2" );
  @composite = ${ xor "signal#sens" "output2" };


  @assign = "sens";

  @newfresh = "sens";

  @signal = "sens";

  @port = "env";

  @input = "env";
  @output = "env";

  @output = "Thermostat->dt";
  @input  = "Thermostat->equip";
  @output = "Equipment->error";

  @transition = "Thermostat->transition#2#MSGm1#in";
  @routine = "Thermostat->transition#2#MSGm1#in";

  @machine = "Thermostat";

  @state = "Thermostat->s4";

  @formula = <expression>;


 endsection TRACE
endprototype
*/


////////////////////////////////////////////////////////////////////////////////
// CONFIGURE API
////////////////////////////////////////////////////////////////////////////////

bool AvmHitOrJumpProcessor::configureImpl()
{
	// SUPER CONFIGURATION
	mConfigFlag = BaseCoverageFilter::configureImpl();

	const WObject * thePROPERTY = Query::getRegexWSequence(getParameterWObject(),
			OR_WID2("property", "PROPERTY"), getParameterWObject());
	if( thePROPERTY != WObject::_NULL_ )
	{
		std::string strScheduler = Query::getRegexWPropertyString(
				thePROPERTY, CONS_WID2("search", "scope"), "GLOBALLY");
		StringTools::toupper( strScheduler );
		mGlobalSearchScopeFlag = ( strScheduler == "GLOBALLY" );


		strScheduler = Query::getWPropertyString(thePROPERTY, "scheduler", "|;|");
		mScheduler = OperatorLib::toOpcode(strScheduler, AVM_OPCODE_NULL);
		if( mScheduler == AVM_OPCODE_NULL )
		{
			if( strScheduler == "ordered" )
			{
				mScheduler = AVM_OPCODE_SEQUENCE;
			}
			else if( strScheduler == "unordered" )
			{
				mScheduler = AVM_OPCODE_INTERLEAVING;
			}
			else if( strScheduler == "regex" )
			{
				mScheduler = AVM_OPCODE_REGEX;
			}
		}
	}


	const WObject * theHEURISTIC = Query::getRegexWSequence(getParameterWObject(),
			OR_WID2("heuristic", "HEURISTIC"), thePROPERTY);
	if( theHEURISTIC != WObject::_NULL_ )
	{
		// the Jump HEIGHT exploration property
		long intAttribute = Query::getRegexWPropertyInt(
				theHEURISTIC, CONS_WID2("jump", "height"), 7);
		if( intAttribute < 0 )
		{
			mJumpHeight = mJumpDelta = AVM_NUMERIC_MAX_SIZE_T;

AVM_IF_DEBUG_FLAG( CONFIGURING )
	AVM_OS_LOG << "Invalid jump height ! => replace by "
			<< mJumpDelta << " >" << std::endl;
AVM_ENDIF_DEBUG_FLAG( CONFIGURING )
		}
		else
		{
			mJumpHeight = mJumpDelta = intAttribute;
		}

		// the Jump trials limit exploration property
		mJumpTrialsLimit = Query::getRegexWPropertyPosSizeT(
			theHEURISTIC, CONS_WID3("jump", "(trials", ")?limit"),
			AVM_NUMERIC_MAX_SIZE_T, AVM_NUMERIC_MAX_SIZE_T);

		// the Hit CONSECUTIVE trace flag property
		mHitConsecutiveFlag = Query::getRegexWPropertyBoolean(
				theHEURISTIC, CONS_WID2("hit", "consecutive"), false);

		// The Folding Flag when checking Trace Point satisfiability in one EC
		mFoldingFlag  = Query::getRegexWPropertyBoolean(
				theHEURISTIC, CONS_WID2("hit", "folding"), true);


		// the Hitter SELECTION only maximal prefix flag property
		mHitMaxFlag = Query::getRegexWPropertyBoolean(
				theHEURISTIC, CONS_WID2("hit", "max"), false);

		// Compilation for coherence and optimization
		if( mHitMaxFlag )
		{
			// the Hit LUCKY wish: Only one try, backtracking off
			mHitLuckyFlag = false;

			// Backtracking enabled !
			mBacktrackFlag = true;

			// the Hit COUNT selection property
			mHitCount = AVM_NUMERIC_MAX_SIZE_T;
		}
		else
		{
			// the Hit LUCKY wish: Only one try, backtracking off
			mHitLuckyFlag = Query::getRegexWPropertyBoolean(
					theHEURISTIC, CONS_WID2("hit", "lucky"), false);

			// Backtracking enabled ?
			mBacktrackFlag = (not mHitLuckyFlag);

			// the Hit COUNT selection property
			mHitCount = Query::getRegexWPropertyPosSizeT(
					theHEURISTIC, CONS_WID2("hit", "count"), 1);
		}


		// the Jump COUNT selection property
		mJumpCount = Query::getRegexWPropertySizeT(
				theHEURISTIC, CONS_WID2("jump", "count"), 1);

		// the Hit FINAL (after objective achieved) flags property mHitFinalFlag
		mHitFinalFlag = Query::getRegexWPropertyBoolean(
				theHEURISTIC, CONS_WID2("hit", "final"), true);

		// the Jump SLICE (after each hit/jump) flags property
		mJumpSliceFlag = (not mBacktrackFlag) &&
				Query::getRegexWPropertyBoolean(
						theHEURISTIC, CONS_WID2("jump", "slice"), true);
	}
	else
	{
		mConfigFlag = false;
	}



	// the Hit Processor configuration
	switch( mScheduler )
	{
		case AVM_OPCODE_INTERLEAVING:
		{
			mHitProcessor = new HitUnorderedProcessor(*this, ENV);
			break;
		}

		case AVM_OPCODE_SEQUENCE:
		case AVM_OPCODE_ATOMIC_SEQUENCE:
		case AVM_OPCODE_SEQUENCE_WEAK:
		case AVM_OPCODE_PRIOR_GT:
		case AVM_OPCODE_NULL:
		default:
		{
			mHitProcessor = new HitOrderedProcessor(*this, ENV);
			break;
		}
	}

	if( mHitProcessor->configure(getParameterWObject()) )
	{
		if( isUnordered() )
		{
			//mHitCount = AVM_NUMERIC_MAX_SIZE_T;
		}
	}
	else
	{
		mConfigFlag = false;
	}

	enablePreprocess( this );

	if( mConfigFlag )
	{
		// Registration to handler DestroyCtx event
		getSymbexEventManager().registerHandlerEventDestroyCtx(this);
	}

	return( mConfigFlag );
}


////////////////////////////////////////////////////////////////////////////////
// REPORT API
////////////////////////////////////////////////////////////////////////////////

void AvmHitOrJumpProcessor::reportMinimum(OutStream & os) const
{
	os << TAB << "FAM< " << QNID() << " , HoJ > " << this->getNameID() << " "
			<< mCoverageStatistics.strCoverageRate(mGoalAchieved) << " ==> "
			<< ((mGoalAchieved || mHitProcessor->goalAchieved()) ?
					"DONE !" : "FAILED !")
			<< std::endl;

	if( (not mHitProcessor->goalAchieved()) && (not mGoalAchieved)
		&& (mJumpTrialsCount > mJumpTrialsLimit) )
	{
		os << TAB << ">>> Retry with a greater < jump#limit="
				<< mJumpTrialsLimit << " > heuristic attribute ! <<<"
				<< std::endl;
	}

	mHitProcessor->reportMinimum(os);
}


void AvmHitOrJumpProcessor::reportDefault(OutStream & os) const
{
	os << TAB << "FAM< " << QNID() << " , HoJ > " << this->getNameID() << "[ "
			<< mHitProcessor->strKind()
			<< " : " << ( mGlobalSearchScopeFlag ? "globally" : "locally" )
			<< " ] < heuristic:" << mHeuristicProperty.mHeuristicEnabled
			<< " , height:" << mJumpDelta << " , hit:";

	((mHitCount < AVM_NUMERIC_MAX_SIZE_T) ? os << mHitCount : os << "<all>")
			<< " , jump:";

	((mJumpCount < AVM_NUMERIC_MAX_SIZE_T) ? os << mJumpCount : os << "<all>")
			<< " ; backtrack:" << mBacktrackFlag << ":"
					<< mCoverageStatistics.mNumberOfBacktrack
			<< " , black_hole:" << mCoverageStatistics.strBlackHoleRate()
			<< " , slice:" << mSliceCount << " >: Coverage "
			<< mCoverageStatistics.strCoverageRate(mGoalAchieved) << " ==> "
			<< ((mGoalAchieved || mHitProcessor->goalAchieved()) ?
					"DONE !" : "FAILED !")
			<< std::endl;

	if( (not mHitProcessor->goalAchieved()) && (not mGoalAchieved)
		&& (mJumpTrialsCount > mJumpTrialsLimit) )
	{
		os << TAB << ">>> Retry with a greater < jump#limit="
				<< mJumpTrialsLimit << " > heuristic attribute ! <<<"
				<< std::endl;
	}

	mHitProcessor->reportDefault(os);

	os << TAB << "FAM< " << QNID() << " , HoJ > " << this->getNameID() << "[ "
			<< mHitProcessor->strKind()
			<< " ] < heuristic:" << mHeuristicProperty.mHeuristicEnabled
			<< " , height:" << mJumpDelta << " , hit:";

	((mHitCount < AVM_NUMERIC_MAX_SIZE_T) ? os << mHitCount : os << "<all>")
			<< " , jump:";

	((mJumpCount < AVM_NUMERIC_MAX_SIZE_T) ? os << mJumpCount : os << "<all>")
			<< " ; backtrack:" << mBacktrackFlag << ":"
					<< mCoverageStatistics.mNumberOfBacktrack
			<< " , black_hole:" << mCoverageStatistics.strBlackHoleRate()
			<< " , slice:" << mSliceCount << " >: Coverage "
			<< mCoverageStatistics.strCoverageRate(mGoalAchieved) << " ==> "
			<< ((mGoalAchieved || mHitProcessor->goalAchieved()) ?
					"DONE !" : "FAILED !")
			<< EOL_FLUSH;
}


////////////////////////////////////////////////////////////////////////////////
// NON-REGRESSION TEST API
////////////////////////////////////////////////////////////////////////////////

void AvmHitOrJumpProcessor::tddRegressionReportImpl(OutStream & os) const
{
	os << TAB << "HIT OR JUMP COVERAGE : "
			<< mCoverageStatistics.strCoverageRate() << " ==> "
			<< (mHitProcessor->goalAchieved() ? "DONE !" : "FAILED !")
			<< EOL_FLUSH;
}

////////////////////////////////////////////////////////////////////////////////
// PROCESS API
////////////////////////////////////////////////////////////////////////////////

//bool AvmHitOrJumpProcessor::preprocess()
//{
//	return( true );
//}
//
//
//bool AvmHitOrJumpProcessor::postprocess()
//{
//	//BaseCoverageFilter::postprocess();
//
//	return( true );
//}


////////////////////////////////////////////////////////////////////////////////
// PRE-FILTER API
////////////////////////////////////////////////////////////////////////////////

bool AvmHitOrJumpProcessor::filteringInitialize()
{
	// Preserve every root context
	mListOfPositiveEC.append( getExecutionQueue().getInitQueue() );
	mInitialRootEC.append( getExecutionQueue().getInitQueue() );

	if( mGlobalSearchScopeFlag )
	{
		mRelativeRootEC.append( getExecutionQueue().getInitQueue() );
	}
	else if( getExecutionQueue().hasInit() )
	{
		mBufferLocalRootEC.splice( getExecutionQueue().getInitQueue() );

		mRelativeRootEC.append( mBufferLocalRootEC.front() );

		// First  Jump Height!
		mJumpHeight = mJumpDelta + mBufferLocalRootEC.front()->getHeight();

		getExecutionQueue().getInitQueue().append( mBufferLocalRootEC.front() );

		mBufferLocalRootEC.pop_front();
	}

	mAbsoluteStopContextFlag = true;

	mJumpTrialsCount = 0;

	getSymbexRequestManager().postRequestContinue( this );

	return( true );
}


bool AvmHitOrJumpProcessor::prefilter()
{
	ecQueue = &( getExecutionQueue().getReadyQueue() );

	mAbsoluteStopContextFlag = false;

	if( ecQueue->nonempty() && (mJumpHeight < AVM_NUMERIC_MAX_SIZE_T) )
	{
		ecQueueIt = ecQueue->begin();
		ecQueueItEnd = ecQueue->end();
		for( ; ecQueueIt != ecQueueItEnd ; )
		{
//			prefilter(*ecQueueIt);

			if( mHitProcessor->goalWillNeverAchieved( *(*ecQueueIt) ) )
			{
				ecQueueIt = ecQueue->erase( ecQueueIt );
			}

			else if( (*ecQueueIt)->getHeight() >= mJumpHeight )
			{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_TRACE << "<<<<< jump< 1 > >>>>> EC< id:"
			<< (*ecQueueIt)->getIdNumber() << " >" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )

				mRelativeLeafEC.append( *ecQueueIt );

				ecQueueIt = ecQueue->erase( ecQueueIt );
			}
			else
			{
				++ecQueueIt;
			}
		}
	}

	return( getExecutionQueue().hasReady() );
}


bool AvmHitOrJumpProcessor::prefilter(ExecutionContext & anEC)
{
	if( mHitProcessor->goalAchieved() && mStopFlag )
	{
		return( false );
	}

	return( true );
}


bool AvmHitOrJumpProcessor::filteringFinalize()
{
	if( mJumpHeight == AVM_NUMERIC_MAX_SIZE_T )
	{
		computeLeafEC(getConfiguration().getExecutionTrace(), mAbsoluteLeafEC);

		mRelativeLeafEC.append( mAbsoluteLeafEC );
		mAbsoluteLeafEC.clear();

		if( mRelativeRootEC.empty() && (mJumpTrialsCount < 1) )
//			&& (mScheduler == AVM_OPCODE_INTERLEAVING) )
		{
			mRelativeRootEC.append(getConfiguration().getExecutionTrace());
		}

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_INFO << "<<<<< AvmHitOrJumpProcessor::filteringFinalize : "
			<< mCoverageStatistics.strCoverageRate() << " >>>>>" << std::endl;

	ExecutionContext::traceMinimum(AVM_OS_TRACE,
			mRelativeRootEC, "the Relative Root EC");

	ExecutionContext::traceMinimum(AVM_OS_TRACE,
			mRelativeLeafEC, "the Relative Leaf EC");
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )

		mAbsoluteStopContextFlag = true;

		handleRequestContinue();
	}

	mCoverageStatistics.copyIfBestCoverageRate(mFinalCoverageStatistics);

	return( BaseCoverageFilter::filteringFinalize() );
}



/**
 * PROCESSOR REQUEST API :> CONITNUE
 * Jump step
 */
void AvmHitOrJumpProcessor::handleRequestContinue()
{
	if( mRelativeRootEC.empty() )
	{
		if( not hojBacktrack() )
		{
			getSymbexRequestManager().postRequestGoalAchieved( this );
		}

		return;
	}

	if( mHitProcessor->hit(mJumpHeight) )
	{
		mSelectionCount = mHitCount;

		mHitCaseFlag = true;

		if( mHitProcessor->goalAchieved() )
		{
			mGoalAchieved = true;

			if( mHitFinalFlag || mHitMaxFlag )
			{
				hojSelectionFinal();
			}

			if( mHitMaxFlag && hojBacktrack() )
			{
				return;
			}

			getSymbexRequestManager().postRequestGoalAchieved( this );

			if( mStopFlag )
			{
				return;
			}
		}
	}
	else if( mHitConsecutiveFlag && (mCoverageStatistics.mNumberOfCovered > 0) )
	{
		getSymbexRequestManager().postRequestGoalAchieved( this );

		return;
	}
	else
	{
		mSelectionCount = mJumpCount;

		mHitCaseFlag = false;
	}

	if( mRelativeLeafEC.nonempty() )
	{
		hojSelection();
	}
	else
	{
		// Locally slice if mJumpSliceFlag
		jumpSlice();

		if( (not mGoalAchieved) && mBacktrackFlag && hojBacktrack() )
		{
			return;
		}

		mAbsoluteStopContextFlag = true;

		mRelativeRootEC.clear();
	}


	if( ++mJumpTrialsCount > mJumpTrialsLimit )
	{
		getSymbexRequestManager().postRequestGoalAchieved( this );

		return;
	}

	else if( mAbsoluteStopContextFlag )
	{
		mCoverageStatistics.copyIfBestCoverageRate(mFinalCoverageStatistics);

		getSymbexRequestManager().postRequestGoalAchieved( this );
	}
	else if( mRelativeRootEC.nonempty() )
	{
		getSymbexRequestManager().postRequestContinue( this );

		getExecutionQueue().appendReady( mRelativeRootEC );

		mJumpHeight = mJumpHeight + mJumpDelta;

		mAbsoluteStopContextFlag = true;
	}

	else if( not hojBacktrack() )
	{
		getSymbexRequestManager().postRequestGoalAchieved( this );
	}
}


/**
 * PROCESSOR REQUEST API :> GOAL_ACHIEVED
 * Ending (positive or negative) locally or globally objective
 */
void AvmHitOrJumpProcessor::handleRequestGoalAchieved()
{
	if( mGlobalSearchScopeFlag || mBufferLocalRootEC.empty() )
	{
		getSymbexRequestManager().postRequestStop( this );
	}
	else
	{
		getExecutionQueue().handleRequestStop();

		mRelativeRootEC.clear();
		mRelativeRootEC.append( mBufferLocalRootEC.front() );


		// Reinitialize parameters for restarting;
		mJumpHeight = mJumpDelta + mBufferLocalRootEC.front()->getHeight();
		mHitProcessor->resetConfig();
		mCoverageStatistics.resetCoverageCounter();


		getExecutionQueue().pushWaiting( mBufferLocalRootEC.front() );

		mBufferLocalRootEC.pop_front();

		mAbsoluteStopContextFlag = true;

		mJumpTrialsCount = 0;

		getSymbexRequestManager().postRequestContinue( this );
	}
}


bool AvmHitOrJumpProcessor::hojBacktrack()
{
	if( mBacktrackHitEC.empty() )
	{
		return( false );
	}

	mFinalCoverageStatistics.copyIfBestCoverageRate( mCoverageStatistics );

	++( mFinalCoverageStatistics.mNumberOfBacktrack );
	++( mCoverageStatistics.mNumberOfBacktrack );

	mBacktrackHitEC.pop_last_to( tmpEC );
	getExecutionQueue().pushWaiting( tmpEC );

	mCoverageStatistics = tmpEC->getUniqInformation()
			->getUniqSpecificInfo< HitOrJumpObjectiveInfo >()
			->getCoverageStatistics();

	mJumpHeight = tmpEC->getHeight() + mJumpDelta;

	mRelativeRootEC.clear();
	mRelativeRootEC.append( tmpEC );

	mAbsoluteStopContextFlag = true;

	getSymbexRequestManager().postRequestContinue( this );

AVM_IF_DEBUG_LEVEL_GTE_MEDIUM
	AVM_OS_INFO << "<<<<< HoJ Backtrack EC< id:"
			<< tmpEC->getIdNumber() << " > where "
			<< mCoverageStatistics.strCoverageRate() << " >>>>>" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_GTE_MEDIUM

	return( true );
}


void AvmHitOrJumpProcessor::hojSelection()
{
AVM_IF_DEBUG_LEVEL_GTE_MEDIUM
	AVM_OS_INFO << "<<<<< HoJ Coverage : "
			<< mCoverageStatistics.strCoverageRate() << " >>>>>" << std::endl;

	//!! current Relative Root& Leaf EC
	ExecutionContext::traceMinimum(AVM_OS_TRACE,
			mRelativeRootEC, "the Relative Root EC");

	ExecutionContext::traceMinimum(AVM_OS_TRACE,
			mRelativeLeafEC, "the Relative Leaf EC");
AVM_ENDIF_DEBUG_LEVEL_GTE_MEDIUM


	// Remove EC when Parent is in any BlackList
	updateRelativeLeaf();

	// Hit or JUMP
	mRelativeRootEC.clear();

	leafCount = mRelativeLeafEC.size();

	if( (leafCount == 0) || (mSelectionCount == 0) )
	{
		mRelativeLeafEC.clear();

		// Locally slice if mJumpSliceFlag
		jumpSlice();

		return;
	}

	randomMax = leafCount - 1;

	if( (mSelectionCount == 1) || (leafCount == 1) )
	{
		jumpOffset = (leafCount == 1) ? 0 : RANDOM::gen_uint(0, randomMax);

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_TRACE << "<<<<< jump< 0 > >>>>> EC< id:"
			<< mRelativeLeafEC[jumpOffset]->getIdNumber() << " >" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )

		if( mHitCaseFlag )
		{
			mHitProcessor->hitSelect( jumpOffset );
		}
		else if( mBacktrackFlag )
		{
			mBacktrackHitEC.remove( mRelativeLeafEC[jumpOffset] );
		}

		mRelativeRootEC.append( mRelativeLeafEC[jumpOffset] );
	}

	else if( mSelectionCount < leafCount )
	{
		jumpOffsetBitset.reset();
		jumpOffsetBitset.resize(leafCount, false);

		for( leafOffset = 0 ; leafOffset < mSelectionCount ; ++leafOffset )
		{
			do
			{
				jumpOffset = RANDOM::gen_uint(0, randomMax);
			}
			while( jumpOffsetBitset[jumpOffset] );

			jumpOffsetBitset[jumpOffset] = true;

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_TRACE << "<<<<< jump< 0 > >>>>> EC< id:"
			<< mRelativeLeafEC[jumpOffset]->getIdNumber() << " >" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )

			if( mHitCaseFlag )
			{
				mHitProcessor->hitSelect( jumpOffset );
			}
			else if( mBacktrackFlag )
			{
				mBacktrackHitEC.remove( mRelativeLeafEC[jumpOffset] );
			}

			mRelativeRootEC.append( mRelativeLeafEC[jumpOffset] );
		}
	}

	else
	{
		for( leafOffset = 0 ; leafOffset < leafCount ; ++leafOffset )
		{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_TRACE << "<<<<< jump< 0 > >>>>> EC< id:"
			<< mRelativeLeafEC[leafOffset]->getIdNumber() << " >" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )

			if( mHitCaseFlag )
			{
				mHitProcessor->hitSelect( leafOffset );
			}
			else if( mBacktrackFlag )
			{
				mBacktrackHitEC.remove( mRelativeLeafEC[jumpOffset] );
			}

			mRelativeRootEC.append( mRelativeLeafEC[leafOffset] );
		}
	}

	mRelativeLeafEC.clear();

	// Locally slice if mJumpSliceFlag
	jumpSlice();


AVM_IF_DEBUG_LEVEL_GTE_MEDIUM
	AVM_OS_TRACE << "<<<<< HoJ Coverage : "
			<< mCoverageStatistics.strCoverageRate() << " >>>>>" << std::endl;

	//!! Next Relative Root EC
	ExecutionContext::traceMinimum(AVM_OS_TRACE,
			mRelativeRootEC, "the Relative Root EC");
AVM_ENDIF_DEBUG_LEVEL_GTE_MEDIUM
}


void AvmHitOrJumpProcessor::hojSelectionFinal()
{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_INFO << "<<<<< HoJ Goal Achieved : "
			<< mCoverageStatistics.strCoverageRate() << " >>>>>" << std::endl;

	ExecutionContext::traceMinimum(AVM_OS_TRACE,
			mRelativeRootEC, "the Relative Root EC");

	ExecutionContext::traceMinimum(AVM_OS_TRACE,
			mRelativeLeafEC, "the Relative Leaf EC");
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )

	// Hit Final
	mRelativeRootEC.clear();

	leafCount = mRelativeLeafEC.size();
	randomMax = leafCount - 1;

	if( mHitMaxFlag )
	{
		mSelectionCount = leafCount;
	}
	else
	{
		for( leafOffset = 0 ; leafOffset < leafCount ; ++leafOffset )
		{
			mRelativeLeafEC[leafOffset]->getwFlags().unsetObjectiveAchievedTrace();
		}
	}

	if( (mSelectionCount == 1) || (leafCount == 1) )
	{
		jumpOffset = (leafCount == 1) ? 0 : RANDOM::gen_uint(0, randomMax);

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_TRACE << "<<<<< jump< goal achieved > >>>>> EC< id:"
			<< mRelativeLeafEC[jumpOffset]->getIdNumber() << " >" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )

		mRelativeLeafEC[jumpOffset]->getwFlags().setObjectiveAchievedTrace();

		mListOfPositiveEC.append( mRelativeLeafEC[jumpOffset] );
	}

	else if( (mSelectionCount < leafCount) && (mSelectionCount > 0) )
	{
		jumpOffsetBitset.reset();
		jumpOffsetBitset.resize(leafCount, false);

		for( leafOffset = 0 ; leafOffset < mSelectionCount ; ++leafOffset )
		{
			do
			{
				jumpOffset = RANDOM::gen_uint(0, randomMax);
			}
			while( jumpOffsetBitset[jumpOffset] );

			jumpOffsetBitset[jumpOffset] = true;

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_TRACE << "<<<<< jump< goal achieved > >>>>> EC< id:"
			<< mRelativeLeafEC[jumpOffset]->getIdNumber() << " >" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )

			mRelativeLeafEC[jumpOffset]->getwFlags().setObjectiveAchievedTrace();

			mListOfPositiveEC.append( mRelativeLeafEC[jumpOffset] );
		}
	}

	else
	{
		for( leafOffset = 0 ; leafOffset < leafCount ; ++leafOffset )
		{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_TRACE << "<<<<< jump< goal achieved > >>>>> EC< id:"
			<< mRelativeLeafEC[leafOffset]->getIdNumber() << " >" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )

			mRelativeLeafEC[leafOffset]->getwFlags().setObjectiveAchievedTrace();

			mListOfPositiveEC.append( mRelativeLeafEC[leafOffset] );
		}
	}

	mRelativeLeafEC.clear();

	// Locally slice if mJumpSliceFlag
	jumpSlice();


AVM_IF_DEBUG_LEVEL_GTE_MEDIUM
	AVM_OS_TRACE << "<<<<< HoJ Coverage : "
			<< mCoverageStatistics.strCoverageRate() << " >>>>>" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_GTE_MEDIUM
}


void AvmHitOrJumpProcessor::updateRelativeLeaf()
{
	jumpOffset = 0;
	leafCount = mRelativeLeafEC.size();

	// Position for Left Shift of non-BlackListed Context Leaf
	randomMax = leafCount;

	// Mark Blacklisted Context Leaf using NULL
	for( leafOffset = 0 ; leafOffset < leafCount ; ++leafOffset )
	{
		tmpEC = mRelativeLeafEC[leafOffset];

		if( mAbsoluteLeafEC.contains( tmpEC ) )
		{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_TRACE << "<<<<< hoj< leaf failed > >>>>> EC< id:"
			<< mRelativeLeafEC[leafOffset]->getIdNumber() << " >" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )

			mRelativeLeafEC[leafOffset] = nullptr;

			if( randomMax == leafCount )
			{
				randomMax = leafOffset;
			}

			continue;
		}

		for( jumpOffset = 0 ; jumpOffset < mJumpDelta ; ++jumpOffset )
		{
			if( tmpEC->isRoot() || mInitialRootEC.contains(tmpEC) )
			{
				break;
			}
			else if( mBlackHoleEC.contains( tmpEC ) )
			{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_TRACE << "<<<<< hoj< leaf failed > >>>>> EC< id:"
			<< mRelativeLeafEC[leafOffset]->getIdNumber() << " >" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )

				mRelativeLeafEC[leafOffset] = nullptr;

				if( randomMax == leafCount )
				{
					randomMax = leafOffset;
				}

				break;
			}

			tmpEC = tmpEC->getPrevious();
		}

		if( (randomMax < leafCount) && (mRelativeLeafEC[leafOffset] != nullptr)  )
		{
			mRelativeLeafEC[randomMax++] = mRelativeLeafEC[leafOffset];
		}

	}

	// Remove NULL Context Leaf
	if( randomMax < leafCount )
	{
		mRelativeLeafEC.resize( randomMax );
	}
}


/**
 * Slice leaf in mSliceableEC
 * w.r.t. the hit/jump/preserved leaf in mRelativeRootEC/mPreservedEC
 * and backward until mJumpDelta
 */
void AvmHitOrJumpProcessor::jumpSlice()
{
//	//!! Blacktrack
//	ExecutionContext::traceMinimum(AVM_OS_TRACE,
//			mBacktrackHitEC, "the Backtrack Hit EC");
//
//	//!! BlackHole ?
//	ExecutionContext::traceMinimum(AVM_OS_TRACE,
//			mBlackHoleEC, "the Black Hole EC");
//
//	//!! DeadLock or Absolute Stop ?
//	ExecutionContext::traceMinimum(AVM_OS_TRACE,
//			mAbsoluteLeafEC, "the Absolute Leaf EC");

	if( mJumpSliceFlag )
	{
		if( mHitLuckyFlag )
		{
			mBlackHoleEC.clear();
			mAbsoluteLeafEC.clear();

			jumpSliceLucky();
		}
		else // if( mBacktrackFlag )
		{
			jumpSliceBacktrack();
		}

AVM_IF_DEBUG_LEVEL_GTE_MEDIUM
	AVM_OS_TRACE << "<<<<< Slice count : " << mSliceCount
			<< " >>>>>" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_GTE_MEDIUM
	}

	mSliceableEC.clear();
}


void AvmHitOrJumpProcessor::updatePreserved()
{
	mJumpPreservedEC.clear();
	mJumpPreservedLeavesEC.clear();

//	ExecutionContext::traceMinimum(AVM_OS_TRACE,
//			mRelativeRootEC, "the Relative Root EC");

	mJumpPreservedLeavesEC.append(mRelativeRootEC);

	ecItEnd = mJumpPreservedLeavesEC.end();
	for( ecIt = mJumpPreservedLeavesEC.begin() ; ecIt != ecItEnd ; ++ecIt )
	{
		tmpEC = (*ecIt);

		mJumpPreservedEC.append( tmpEC );

		if( tmpEC->isRoot() || mInitialRootEC.contains(tmpEC) )
		{
			continue;
		}

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_TRACE << "<<<<< preserved EC< id: "
			<< tmpEC->getIdNumber() << " > >>>>> " << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )

		for( jumpOffset = 1 ; jumpOffset < mJumpDelta ; ++jumpOffset )
		{
			tmpEC = tmpEC->getPrevious();

			if( tmpEC->isRoot() || mInitialRootEC.contains(tmpEC) ||
					mJumpPreservedEC.contains( tmpEC ) )
			{
				continue;
			}

			mJumpPreservedEC.append( tmpEC );

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_TRACE << "<<<<< preserved EC< id: "
			<< tmpEC->getIdNumber() << " > >>>>> " << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
		}
	}
}


void AvmHitOrJumpProcessor::jumpSliceLucky()
{
	updatePreserved();

//	ExecutionContext::traceMinimum(AVM_OS_TRACE,
//			mJumpPreservedEC, "the Jump Preserved EC");
//
//	ExecutionContext::traceMinimum(AVM_OS_TRACE,
//			mJumpPreservedLeavesEC, "the Jump Preserved Leaves EC");


	ecItEnd = mJumpPreservedLeavesEC.end();
	for( ecIt = mJumpPreservedLeavesEC.begin() ; ecIt != ecItEnd ; ++ecIt )
	{
		tmpEC = (*ecIt);

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_TRACE << "<<<<< jumpSlice from preserved leaf EC< id: "
			<< tmpEC->getIdNumber() << " > >>>>> " << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )

		if( tmpEC->isRoot() || mInitialRootEC.contains(tmpEC) )
		{
			continue;
		}

		for( jumpOffset = 0 ; jumpOffset < mJumpDelta ; ++jumpOffset )
		{
			tmpEC = tmpEC->getPrevious();
			if( tmpEC->isRoot() || mInitialRootEC.contains(tmpEC) )
			{
				break;
			}

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_TRACE << "<<<<< jumpSlice from preserved EC< id: "
			<< tmpEC->getIdNumber() << " > >>>>> " << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )

			endChildEC = tmpEC->end();
			for( itChildEC = tmpEC->begin() ; itChildEC != endChildEC ; )
			{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_TRACE << "<<<<< jumpSlice ??? EC< id: " << (*itChildEC)->getIdNumber()
			<< " > >>>>> count:> " << mSliceCount << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )

				if( mJumpPreservedEC.contains( *itChildEC ) )
				{
					++itChildEC;
				}
				else
				{
					prevEC = (*itChildEC);

					itChildEC = tmpEC->eraseChildContext( itChildEC );
					prevEC->setContainer( nullptr );

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_TRACE << "<<<<< jumpSlice EC< id: " << prevEC->getIdNumber()
			<< " > >>>>> " << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )

					mSliceCount = mSliceCount + AbstractProcessorUnit::remove(
							prevEC, AVM_OS_TRACE, "<<<<< jumpSliceLucky" );

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_TRACE << "<<<<< jumpSlice count: " << mSliceCount
			<< " >>>>>" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
				}
			}
		}
	}
}


void AvmHitOrJumpProcessor::jumpSliceBacktrack()
{
	//!! BlackHole ?
	mSliceableEC.splice( mBlackHoleEC );

	//!! DeadLock or Absolute Stop ?
	mSliceableEC.splice( mAbsoluteLeafEC );

//	mSliceableEC.unique();

	ecItEnd = mSliceableEC.end();
	for( ecIt = mSliceableEC.begin() ; ecIt != ecItEnd ; ++ecIt )
	{
		tmpEC = (*ecIt);

		for( jumpOffset = 0 ; jumpOffset <= mJumpDelta ; ++jumpOffset )
		{
			if( (tmpEC->hasNext() && (jumpOffset > 0)) || tmpEC->isRoot() ||
					mListOfPositiveEC.contains(tmpEC) )
			{
				break;
			}

			prevEC = tmpEC->getPrevious();

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_TRACE << "<<<<< jumpSlice EC< id: " << tmpEC->getIdNumber()
			<< " > >>>>>" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )

			mSliceCount = mSliceCount + AbstractProcessorUnit::remove(
					tmpEC, AVM_OS_TRACE, "<<<<< jumpSliceBacktrack" );

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_TRACE << "<<<<< jumpSlice count: " << mSliceCount
			<< " >>>>>" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )


			tmpEC = prevEC;
		}
	}
}


////////////////////////////////////////////////////////////////////////////////
// POST-FILTER API
////////////////////////////////////////////////////////////////////////////////

bool AvmHitOrJumpProcessor::postfilter()
{
//	ecQueue = &( getExecutionQueue().getResultQueue() );
//	ecQueueItEnd = ecQueue->end();
//	for( ecQueueIt = ecQueue->begin() ; ecQueueIt != ecQueueItEnd ; )
//	{
//		if( postfilter(*ecQueueIt) )
//		{
//			++ecQueueIt;
//		}
//		else
//		{
//			ecQueueIt = ecQueue->erase(ecQueueIt);
//		}
//	}

	return( getExecutionQueue().hasResult() );
}


bool AvmHitOrJumpProcessor::postfilter(ExecutionContext & anEC)
{
//	if( mHitProcessor->hit(anEC) )
//	{
//		if( mHitProcessor->goalAchieved() && mStopFlag )
//		{
//			return( false );
//		}
//	}

	return( true );
}


/**
 * IHandlerEventDestroyCtx API
 * Destroy Execution Context
 */
void AvmHitOrJumpProcessor::handleEventDestroyCtx(ExecutionContext * anEC)
{
	mBacktrackHitEC.remove( anEC );
}



////////////////////////////////////////////////////////////////////////////
// FINAL SLICING TOOLS
////////////////////////////////////////////////////////////////////////////

bool AvmHitOrJumpProcessor::isSliceableContext(ExecutionContext & anEC) const
{
	if( mHitProcessor->goalAchieved() )
	{
		return( anEC.getFlags().noneObjectiveAchievedTrace()
				&& (not mInitialRootEC.contains(& anEC)) );
	}
	else
	{
		return( anEC.getFlags().noneCoverageElementTrace()
				&& (not mInitialRootEC.contains(& anEC))
				&& (not mListOfPositiveEC.contains(& anEC)) );
	}
}


} /* namespace sep */
