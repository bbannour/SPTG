/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 31 janv. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "HitUnorderedProcessor.h"

#include <fml/operator/OperatorManager.h>

#include <fml/runtime/ExecutionContext.h>

#include <fam/hitorjump/AvmHitOrJumpProcessor.h>


namespace sep
{


/**
 * CONSTRUCTOR
 * Default
 */
HitUnorderedProcessor::HitUnorderedProcessor(
		AvmHitOrJumpProcessor & hojProcessor, EvaluationEnvironment & anENV)
: BaseHitProcessor(hojProcessor, anENV,
		OperatorManager::OPERATOR_INTERLEAVING),

mHitCoverageBitset( ),
mHitSelectedCoverageBitset( ),
mHitSelectedEC( )
{
	//!! NOTHING
}


////////////////////////////////////////////////////////////////////////////////
// CONFIGURE API
////////////////////////////////////////////////////////////////////////////////

bool HitUnorderedProcessor::resetConfig()
{
	return( BaseHitProcessor::resetConfig() );
}


////////////////////////////////////////////////////////////////////////////////
// HIT FILTERING API
////////////////////////////////////////////////////////////////////////////////

bool HitUnorderedProcessor::goalWillNeverAchieved(ExecutionContext * anEC)
{
	if( not isPureStateTransitionNatureFlag )
	{
		return( false );
	}

	else
	{
//		traceOffset = 0;
//		for( ; traceOffset != mCoverageStatistics.mNumberOfElements ; ++traceOffset )
//		{
//			if( mCoverageStatistics.coverageBitset.test(traceOffset) )
//			{
//				//!! continue;
//			}
//			else if( BaseHitProcessor::willNeverHit(
//					anEC,mTraceObjective[traceOffset]) )
//			{
//				if( not BaseHitProcessor::hit(anEC,mTraceObjective[traceOffset]) )
//				{
//					++mCoverageStatistics.mNumberOfBlackHole;
//
//					mBlackHoleEC.append(anEC);
//
//AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
//	AVM_OS_TRACE << "<<<<< HoJ< BLACK HOLE > >>>>>" << std::endl
//			<< "EC:> " << anEC->str_min() << std::endl;
//AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
//
//					return( true );
//				}
//			}
//		}

		return( false );
	}
}


bool HitUnorderedProcessor::hit(avm_size_t jumpHeight)
{
	if( goalAchieved() )
	{
		return( true );
	}

	mJumpHeight = jumpHeight;


	// ALGO for UNORDERED
	mHitCount = 0;
	mMaxHitEC.clear();
	mHitCoverageBitset.clear();

	if( mRelativeRootEC.singleton() )
	{
		hit(mRelativeRootEC.front(), mCoverageStatistics.mCoverageBitset, 0);
	}
	else
	{
		ExecutionContext::child_iterator itChildEC;
		ExecutionContext::child_iterator endChildEC;

		ecItEnd = mRelativeRootEC.end();
		for( ecIt = mRelativeRootEC.begin() ; ecIt != ecItEnd ; ++ecIt )
		{
			itChildEC = (*ecIt)->begin();
			endChildEC = (*ecIt)->end();
			for( ; itChildEC != endChildEC ; ++itChildEC )
			{
				hit((*itChildEC), hitCoverageBitset(*ecIt), 0);
			}
		}

		mHitSelectedEC.clear();
		mHitSelectedCoverageBitset.clear();
	}


	if( mHitCount > 0 )
	{
		mCoverageStatistics.addCoveredElement( mHitCount );

		// based on mCoverageStatistics.mNumberOfCovered
		if( mCoverageStatistics.goalAchieved() )
		{
			mCoverageStatistics.mCoverageBitset.set();
		}

		mRelativeLeafEC.clear();

		hitOffsetEnd = mMaxHitEC.size();
		for( hitOffset = 0 ; hitOffset != hitOffsetEnd ; ++hitOffset )
		{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_TRACE << "<<<<< hit< candidate > >>>>> EC< id:"
			<< mMaxHitEC[ hitOffset ]->getIdNumber() << " >" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )

			mMaxHitEC[ hitOffset ]->setWeight(0);

			mRelativeLeafEC.append( mMaxHitEC[ hitOffset ] );
		}

		return( true );
	}

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

	return( false );
}


void HitUnorderedProcessor::hit(ExecutionContext * anEC,
		Bitset coverageBitset, avm_size_t hitCount)
{
	if( mBlackHoleEC.contains(anEC) )
	{
		return;
	}

	avm_size_t saveHitCount = hitCount;

	traceOffset = 0;
	for( ; traceOffset != mCoverageStatistics.mNumberOfElements ; ++traceOffset )
	{
		if( coverageBitset.test(traceOffset) )
		{
			//!! continue;
		}
		else if( BaseHitProcessor::hit(anEC, mTraceObjective[traceOffset]) )
		{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_TRACE << "<<<<< hit< 1 > >>>>> EC< id:"
			<< anEC->getIdNumber() << " >" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )

			anEC->getwFlags().setCoverageElementTrace();

			anEC->addInfo(mHitOrJumpProcessor, mTraceObjective[traceOffset]);

			coverageBitset.set(traceOffset, true),

			++hitCount;

			if( not mHitOrJumpProcessor.mFoldingFlag )
			{
				break;
			}
		}
	}


	if( (saveHitCount == hitCount) )
	{
		if( mHitOrJumpProcessor.mHitConsecutiveFlag && coverageBitset.any() )
		{
			// TODO
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_TRACE << "<<<<< hit#consecutive< FAILED > >>>>> EC< id:"
			<< anEC->getIdNumber() << " >" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )

			return;
		}
		else if( willNeverHit(anEC, coverageBitset) )
		{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_TRACE << "<<<<< hit#never< 1 > >>>>> EC< id:"
			<< anEC->getIdNumber() << " >" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )

			return;
		}
	}


	if( hitCount == mCoverageStatistics.getNumberOfUncovered() )
	{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	anEC->getwFlags().setObjectiveAchievedTrace();

	AVM_OS_TRACE << "<<<<< hit< goal achieved > >>>>> EC< id:"
			<< anEC->getIdNumber() << " >" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )

		if( hitCount > mHitCount )
		{
			if( mBacktrackFlag )
			{
				hitOffsetEnd = mMaxHitEC.size();
				for( hitOffset = 0 ; hitOffset != hitOffsetEnd ; ++hitOffset )
				{
					saveBacktrackable(mMaxHitEC[hitOffset],
							mHitCoverageBitset[hitOffset], mHitCount);
				}
			}

			mMaxHitEC.clear();
			mHitCoverageBitset.clear();

			mHitCount = hitCount;
		}

		mMaxHitEC.push_back( anEC );
		mHitCoverageBitset.push_back(coverageBitset);
	}

	else if( anEC->hasNext() )
	{
		ExecutionContext::child_iterator itChildEC = anEC->begin();
		ExecutionContext::child_iterator endChildEC = anEC->end();
		for( ; itChildEC != endChildEC ; ++itChildEC )
		{
			hit((*itChildEC), coverageBitset, hitCount);
		}
	}

	else if( isAbsoluteLeaf(anEC) )
	{
		//!! CONTINUE
	}

	else if( hitCount > mHitCount )
	{
		if( mBacktrackFlag )
		{
			hitOffsetEnd = mMaxHitEC.size();
			for( hitOffset = 0 ; hitOffset != hitOffsetEnd ; ++hitOffset )
			{
				saveBacktrackable(mMaxHitEC[hitOffset],
						mHitCoverageBitset[hitOffset], mHitCount);
			}
		}

		mMaxHitEC.clear();
		mHitCoverageBitset.clear();

		mHitCount = hitCount;

		mMaxHitEC.push_back( anEC );
		mHitCoverageBitset.push_back(coverageBitset);
	}

	else if( hitCount > 0 )
	{
		if( hitCount == mHitCount )
		{
			mMaxHitEC.push_back( anEC );
			mHitCoverageBitset.push_back(coverageBitset);
		}
		else
		{
			anEC->setWeightMax();

			if( mBacktrackFlag )
			{
				saveBacktrackable(anEC, coverageBitset, hitCount);
			}
		}
	}

	else if( hitCount == 0 )
	{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_TRACE << "<<<<< nop >>>>> EC< id:"
			<< anEC->getIdNumber() << " >" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )

		anEC->setWeightMax();

		if( mBacktrackFlag )
		{
			saveBacktrackable(anEC, coverageBitset, hitCount);
		}
	}
}


void HitUnorderedProcessor::hitSelect(avm_size_t jumpOffset)
{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_TRACE << "<<<<< hit< 0 > >>>>> EC< id:"
			<< mMaxHitEC[ jumpOffset ]->getIdNumber() << " >" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )

	mMaxHitEC[ jumpOffset ]->setWeight(0);

	mCoverageStatistics.mCoverageBitset = mHitCoverageBitset[ jumpOffset ];

	mHitSelectedEC.append( mMaxHitEC[ jumpOffset ] );
	mHitSelectedCoverageBitset.append( mHitCoverageBitset[ jumpOffset ] );
}


Bitset & HitUnorderedProcessor::hitCoverageBitset(ExecutionContext * anEC)
{
	hitOffsetEnd = mHitSelectedEC.size();
	for( hitOffset = 0 ; hitOffset != hitOffsetEnd ; ++hitOffset )
	{
		if( mHitSelectedEC[hitOffset] == anEC )
		{
			return( mHitSelectedCoverageBitset[hitOffset] );
		}
	}

	return( mCoverageStatistics.mCoverageBitset );
}


////////////////////////////////////////////////////////////////////////////////
// FILTERING TOOLS
////////////////////////////////////////////////////////////////////////////////

void HitUnorderedProcessor::saveBacktrackable(ExecutionContext * anEC,
		Bitset & coverageBitset, avm_size_t hitCount)
{
	if( anEC->hasNext() )
	{
		//!! NOTHING
	}

	else if( willNeverHit(anEC, coverageBitset) )
	{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_TRACE << "<<<<< hit#never< 1 > >>>>> EC< id:"
		<< anEC->getIdNumber() << " >" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	}

	else
	{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_TRACE << "<<<<< hit< backtract > >>>>> EC< id:"
		<< anEC->getIdNumber() << " >" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )

		anEC->getUniqInformation()->getUniqHitOrJumpObjectiveInfo()->
				setCoverageStatistics( mCoverageStatistics, coverageBitset );

		mBacktrackHitEC.append( anEC );
	}
}


bool HitUnorderedProcessor::willNeverHit(
		ExecutionContext * anEC, Bitset & coverageBitset)
{
	if( isAbsoluteLeaf(anEC) )
	{
		return( true );
	}
	else if( not isPureStateTransitionNatureFlag )
	{
		return( false );
	}

	traceOffset = 0;
	for( ; traceOffset != mCoverageStatistics.mNumberOfElements ; ++traceOffset )
	{
		if( coverageBitset.test(traceOffset) )
		{
			//!! continue;
		}
		else if( BaseHitProcessor::willNeverHit(
				anEC,mTraceObjective[traceOffset]) )
		{
			++mCoverageStatistics.mNumberOfBlackHole;

			mBlackHoleEC.append(anEC);

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_TRACE << "<<<<< HoJ< BLACK HOLE > >>>>>" << std::endl
			<< "EC:> " << anEC->str_min() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

			return( true );
		}
	}

	return( false );
}


} /* namespace sep */
