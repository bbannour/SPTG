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

#include "HitOrderedProcessor.h"

#include <fml/operator/OperatorManager.h>

#include <fml/runtime/ExecutionContext.h>

#include <famcore/hitorjump/AvmHitOrJumpProcessor.h>


namespace sep
{


/**
 * CONSTRUCTOR
 * Default
 */
HitOrderedProcessor::HitOrderedProcessor(
		AvmHitOrJumpProcessor & hojProcessor, EvaluationEnvironment & anENV)
: BaseHitProcessor(hojProcessor, anENV , OperatorManager::OPERATOR_SEQUENCE ),
mLastObjective( )
{
	//!! NOTHING
}


////////////////////////////////////////////////////////////////////////////////
// CONFIGURE API
////////////////////////////////////////////////////////////////////////////////

bool HitOrderedProcessor::configure(const WObject * wfParameterObject)
{
	bool mConfigFlag = BaseHitProcessor::configure(wfParameterObject);

	if( isPureStateTransitionNatureFlag && mTraceObjective.hasOperand() )
	{
		mLastObjective = mTraceObjective.last();
	}

	return( mConfigFlag );
}


bool HitOrderedProcessor::resetConfig()
{
	return( BaseHitProcessor::resetConfig() );
}

////////////////////////////////////////////////////////////////////////////////
// HIT FILTERING API
////////////////////////////////////////////////////////////////////////////////

bool HitOrderedProcessor::goalWillNeverAchieved(ExecutionContext & anEC)
{
	if( mLastObjective.invalid() )
	{
		return( false );
	}

	else if( BaseHitProcessor::hit(anEC, mLastObjective) )
	{
		return( false );
	}

	else if( willNeverHit(anEC, mLastObjective) )
	{
		++mCoverageStatistics.mNumberOfBlackHole;

		mBlackHoleEC.append(& anEC);

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_TRACE << "<<<<< goalWillNeverAchieved< BLACK HOLE > >>>>>" << std::endl
			<< "EC:> " << anEC.str_min() << std::endl
			<< str_indent( mLastObjective ) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

		return( true );
	}

	else
	{
		return( false );
	}
}



bool HitOrderedProcessor::hit(std::size_t jumpHeight)
{
	if( goalAchieved() )
	{
		return( true );
	}

	mJumpHeight = jumpHeight;


	// ALGO for ORDERED
	mMaxHitCount = 0;
	mMaxHitEC.clear();

	ecIt = mRelativeRootEC.begin();
	ecItEnd = mRelativeRootEC.end();
	for( ; ecIt != ecItEnd ; ++ecIt )
	{
		for( const auto & itChildEC : (*ecIt)->getChildContexts() )
		{
			hit(*itChildEC, mCoverageStatistics.mNumberOfCovered, 0);
		}
	}

	if( mMaxHitCount > 0 )
	{
		traceOffset = mCoverageStatistics.mNumberOfCovered;
		mCoverageStatistics.addCoveredElement( mMaxHitCount );
		// set the coverage bitset
		for( ; traceOffset < mCoverageStatistics.mNumberOfCovered ; ++traceOffset )
		{
			mCoverageStatistics.mCoverageBitset.set(traceOffset, true);
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


void HitOrderedProcessor::hit(ExecutionContext & anEC,
		std::size_t uncoveredOffset, std::size_t hitCount)
{
	if( mBlackHoleEC.contains(& anEC) )
	{
		return;
	}

	std::size_t saveHitCount = hitCount;

	for( ; uncoveredOffset < mCoverageStatistics.mNumberOfElements ;
			++uncoveredOffset )
	{
		if( BaseHitProcessor::hit(anEC, mTraceObjective[uncoveredOffset]) )
		{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_TRACE << "<<<<< hit< cover > >>>>> EC< id:" << anEC.getIdNumber()
			<< " > |= " << mTraceObjective[uncoveredOffset].str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

			anEC.getwFlags().setCoverageElementTrace();

			anEC.addInfo(mHitOrJumpProcessor, mTraceObjective[uncoveredOffset]);

			++hitCount;

			if( not mHitOrJumpProcessor.mFoldingFlag )
			{
				++uncoveredOffset;
				break;
			}
		}

		else
		{
			if( mHitOrJumpProcessor.mHitConsecutiveFlag &&
				(saveHitCount == hitCount) && (uncoveredOffset > 0) )
			{
				// TODO
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_TRACE << "<<<<< hit#consecutive< FAILED > >>>>> EC< id:"
			<< anEC.getIdNumber() << " >" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )

				return;
			}

			if( willNeverReached(anEC, mTraceObjective[uncoveredOffset]) )
			{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_TRACE << "<<<<< hit#never< 1 > >>>>> EC< id:"
			<< anEC.getIdNumber() << " >" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )

				return;
			}

			break;
		}
	}


	if( hitCount == mCoverageStatistics.getNumberOfUncovered() )
	{
		anEC.getwFlags().setObjectiveAchievedTrace();

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_TRACE << "<<<<< hit< goal achieved > >>>>> EC< id:"
			<< anEC.getIdNumber() << " >" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )


		if( hitCount > mMaxHitCount )
		{
			if( mBacktrackFlag )
			{
				hitOffsetEnd = mMaxHitEC.size();
				for( hitOffset = 0 ; hitOffset != hitOffsetEnd ; ++hitOffset )
				{
					saveBacktrackable(*(mMaxHitEC[hitOffset]), mMaxHitCount);
				}
			}

			mMaxHitEC.clear();

			mMaxHitCount = hitCount;
		}

		mMaxHitEC.push_back( & anEC );
	}

	else if( anEC.hasNext() )
	{
		for( auto & itChildEC : anEC.getChildContexts() )
		{
			hit(*itChildEC, uncoveredOffset, hitCount);
		}
	}

	else if( isAbsoluteLeaf(anEC) )
	{
		//!! CONTINUE
	}

	else if( hitCount > mMaxHitCount )
	{
		if( mBacktrackFlag )
		{
			hitOffsetEnd = mMaxHitEC.size();
			for( hitOffset = 0 ; hitOffset != hitOffsetEnd ; ++hitOffset )
			{
				saveBacktrackable(*(mMaxHitEC[hitOffset]), mMaxHitCount);
			}
		}

		mMaxHitEC.clear();

		mMaxHitCount = hitCount;

		mMaxHitEC.push_back( & anEC );
	}

	else if( (hitCount > 0) )
	{
		if( hitCount == mMaxHitCount )
		{
			mMaxHitEC.push_back( & anEC );
		}
		else
		{
			anEC.setWeightMax();

			if( mBacktrackFlag )
			{
				saveBacktrackable(anEC, hitCount);
			}
		}
	}

	else if( hitCount == 0 )
	{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_TRACE << "<<<<< nop >>>>> EC< id:"
			<< anEC.getIdNumber() << " >" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )

		anEC.setWeightMax();

		if( mBacktrackFlag )
		{
			saveBacktrackable(anEC, hitCount);
		}
	}
}


void HitOrderedProcessor::hitSelect(std::size_t jumpOffset)
{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_TRACE << "<<<<< hit< jump:" << jumpOffset << " >>>>> EC< id:"
			<< mMaxHitEC[ jumpOffset ]->getIdNumber() << " >" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )

	mMaxHitEC[ jumpOffset ]->setWeight(0);
}


////////////////////////////////////////////////////////////////////////////////
// FILTERING TOOLS
////////////////////////////////////////////////////////////////////////////////

void HitOrderedProcessor::saveBacktrackable(
		ExecutionContext & anEC, std::size_t hitCount)
{
	if( anEC.hasNext() )
	{
		//!! NOTHING
	}

	else if( willNeverReached(anEC, mTraceObjective
			[ mCoverageStatistics.getNumberOfCovered() + hitCount ]) )
	{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_TRACE << "<<<<< hit#never< 1 > >>>>> EC< id:"
		<< anEC.getIdNumber() << " >" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	}

	else
	{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_TRACE << "<<<<< hit< backtract > >>>>> EC< id:"
		<< anEC.getIdNumber() << " >" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )

		anEC.getUniqInformation()
				->getUniqSpecificInfo< HitOrJumpObjectiveInfo >()
				->setCoverageStatistics( mCoverageStatistics , hitCount );

		mBacktrackHitEC.append( & anEC );
	}
}


bool HitOrderedProcessor::willNeverReached(
		ExecutionContext & anEC, const BF & arg)
{
	if( isAbsoluteLeaf(anEC) )
	{
		return( true );
	}

	else if( BaseHitProcessor::willNeverHit(anEC, arg) )
	{
		++mCoverageStatistics.mNumberOfBlackHole;

		mBlackHoleEC.append(& anEC);

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_TRACE << "<<<<< HoJ< BLACK HOLE > >>>>>" << std::endl
			<< "EC:> " << anEC.str_min() << std::endl
			<< str_indent( arg ) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

		return( true );
	}
	else
	{
		return( false );
	}
}


} /* namespace sep */
