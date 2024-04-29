/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 5 févr. 2015
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVMCOVERAGESTATISTICS_H_
#define AVMCOVERAGESTATISTICS_H_

#include <collection/Bitset.h>

#include <util/avm_numeric.h>
#include <util/avm_util.h>


namespace sep
{

class OutStream;


class AvmCoverageStatistics
{

public:
	/*
	 * ATTRIBUTES
	 */
	Bitset     mCoverageBitset;

	std::size_t mNumberOfElements;
	std::size_t mNumberOfCovered;

	std::size_t mCoverageRateGoal;
	std::size_t mCoverageRestGoal;

	std::size_t mBackupOfCovered;

	std::size_t mNumberOfBacktrack;

	std::size_t mNumberOfFailedStep;
	std::size_t mNumberOfFailedHeuristic;

	std::size_t mNumberOfBlackHole;
	std::size_t mNumberOfBlackHoleTest;


public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmCoverageStatistics(std::size_t objRate = 100, std::size_t objRest = 0)
	: mCoverageBitset( 0 , false ),
	mNumberOfElements( 0 ),
	mNumberOfCovered( 0 ),

	mCoverageRateGoal( objRate ),
	mCoverageRestGoal( objRest ),

	mBackupOfCovered( 0 ),

	mNumberOfBacktrack( 0 ),

	mNumberOfFailedStep( 0 ),
	mNumberOfFailedHeuristic( 0 ),

	mNumberOfBlackHole( 0 ),
	mNumberOfBlackHoleTest( 0 )
	{
		//!! NOTHING
	}


	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	AvmCoverageStatistics(const AvmCoverageStatistics & aCoverageStatistics)
	: mCoverageBitset( aCoverageStatistics.mCoverageBitset ),
	mNumberOfElements( aCoverageStatistics.mNumberOfElements ),
	mNumberOfCovered( aCoverageStatistics.mNumberOfCovered ),

	mCoverageRateGoal( aCoverageStatistics.mCoverageRateGoal ),
	mCoverageRestGoal( aCoverageStatistics.mCoverageRestGoal ),

	mBackupOfCovered( aCoverageStatistics.mBackupOfCovered ),

	mNumberOfBacktrack( aCoverageStatistics.mNumberOfBacktrack ),

	mNumberOfFailedStep( aCoverageStatistics.mNumberOfFailedStep ),
	mNumberOfFailedHeuristic( aCoverageStatistics.mNumberOfFailedHeuristic ),

	mNumberOfBlackHole( aCoverageStatistics.mNumberOfBlackHole ),
	mNumberOfBlackHoleTest( aCoverageStatistics.mNumberOfBlackHoleTest )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~AvmCoverageStatistics()
	{
		//!! NOTHING
	}

	/**
	 * Copy if coverage rate is best
	 */
	inline double coverageRate() const
	{
		return( (mNumberOfElements == 0) ?  0.0  :
				(static_cast< double >(mNumberOfCovered) / mNumberOfElements) );
	}

	inline void copyIfBestCoverageRate(const AvmCoverageStatistics & aStat)
	{
		if( (aStat.mNumberOfElements > 0) && ((mNumberOfElements == 0) ||
			(this->coverageRate() < aStat.coverageRate()) ||
			(mNumberOfElements < aStat.mNumberOfElements)) )
		{
			mCoverageBitset = aStat.mCoverageBitset;

			mNumberOfElements = aStat.mNumberOfElements;
			mNumberOfCovered  = aStat.mNumberOfCovered;

			mCoverageRateGoal = aStat.mCoverageRateGoal;
			mCoverageRestGoal = aStat.mCoverageRestGoal;

			mBackupOfCovered = aStat.mBackupOfCovered;

			mNumberOfBacktrack = aStat.mNumberOfBacktrack;

			mBackupOfCovered = aStat.mBackupOfCovered;
			mNumberOfFailedStep = aStat.mNumberOfFailedStep;
			mNumberOfFailedHeuristic = aStat.mNumberOfFailedHeuristic;

			mNumberOfBlackHole = aStat.mNumberOfBlackHole;
			mNumberOfBlackHoleTest = aStat.mNumberOfBlackHoleTest;
		}
	}


	/**
	 * RESETTER
	 */
	inline void resetCounter()
	{
		mCoverageBitset.clear();

		mNumberOfElements  = 0;
		mNumberOfCovered   = 0;
		mBackupOfCovered   = 0;
		mNumberOfBacktrack = 0;

		mNumberOfFailedStep = 0;
		mNumberOfFailedHeuristic = 0;
	}

	inline void resetCoverageCounter()
	{
		mCoverageBitset.reset();

		mNumberOfCovered = 0;
		mBackupOfCovered = 0;

		mNumberOfFailedStep = 0;
		mNumberOfFailedHeuristic = 0;
	}

	inline void resetFailedStep()
	{
		mNumberOfFailedStep = 0;
		mNumberOfFailedHeuristic = 0;
	}

	inline void setFailedHeuristic()
	{
		mNumberOfFailedHeuristic = 1;
	}


	/**
	 * mNumberOfElements
	 */
	inline void addUncoveredElement()
	{
		++mNumberOfElements;
	}

	inline void addUncoveredElement(std::size_t count)
	{
		mNumberOfElements += count;
	}


	inline std::size_t getNumberOfElements() const
	{
		return mNumberOfElements;
	}

	inline void setNumberOfElements(std::size_t count)
	{
		mNumberOfElements = count;
	}


	/**
	 * mNumberOfCovered
	 */
	inline void addCoveredElement(std::size_t count = 1)
	{
		mNumberOfCovered += count;
	}


	inline std::size_t getNumberOfCovered() const
	{
		return mNumberOfCovered;
	}

	inline void setNumberOfCovered(std::size_t count)
	{
		mNumberOfCovered = count;
	}


	/**
	 * objectiveRate
	 * objectiveRest
	 */
	inline void setObjectives(std::size_t objRate = 100, std::size_t objRest = 0)
	{
		mCoverageRateGoal = objRate;
		mCoverageRestGoal = objRest;
	}


	/**
	 * mBackupOfCovered
	 * mNumberOfCovered
	 */
	inline void backupCovered()
	{
		mBackupOfCovered = mNumberOfCovered;
	}

	inline bool hasNewlyCovered()
	{
		return( mBackupOfCovered < mNumberOfCovered );
	}

	inline bool isNewlyFailedStep()
	{
		return( mBackupOfCovered == mNumberOfCovered );
	}


	/**
	 * mNumberOfElements
	 * mNumberOfCovered
	 */
	inline std::size_t getNumberOfUncovered() const
	{
		return( mNumberOfElements - mNumberOfCovered );
	}


	/**
	 * mNumberOfElements
	 * mNumberOfFailedStep
	 */
	inline bool hasFailedStep() const
	{
		return( mNumberOfFailedStep > 0 );
	}

	inline bool isSeriouslyFailedStep() const
	{
		return( (mNumberOfFailedStep % mNumberOfElements) == 0 );
	}

	inline bool isSuccessfulStep() const
	{
		return( mNumberOfFailedStep == 0 );
	}

	/**
	 * mNumberOfFailedStep
	 * mBackupOfCovered
	 * mNumberOfCovered
	 */
	inline bool updateFailedStep()
	{
		if( mBackupOfCovered == mNumberOfCovered )
		{
			++mNumberOfFailedStep;

			return( true );
		}

		return( false );
	}


	/**
	 * mNumberOfFailedHeuristic
	 * mNumberOfFailedStep
	 * mBackupOfCovered
	 * mNumberOfCovered
	 */
	inline bool updateFailedHeuristic()
	{
		if( mNumberOfFailedHeuristic > 0 )
		{
			++mNumberOfFailedHeuristic;

			return( isSeriouslyFailedStep() );
		}

		return( true );
	}


	/**
	 * mNumberOfBlackHole
	 * mNumberOfBlackHoleTest
	 */
	inline std::string strBlackHoleRate() const
	{
		return( OSS() << mNumberOfBlackHole << "/" << mNumberOfBlackHoleTest );
	}


	/**
	 * Coverage Test
	 */
	inline bool goalAchieved() const
	{
		// AssertTrue( mCoverageBitset.allTrue() ) ?
		return( mNumberOfCovered == mNumberOfElements );
	}

	inline bool goalAchievedRate() const
	{
		return( ((100 * mNumberOfCovered) / mNumberOfElements)
				>= mCoverageRateGoal );
	}

	inline bool goalAchievedRest() const
	{
		return( (mNumberOfElements - mNumberOfCovered) <= mCoverageRestGoal );
	}

	inline bool hasCovered() const
	{
		return( mNumberOfCovered > 0 );
	}

	inline bool hasUncovered() const
	{
		// AssertTrue( mCoverageBitset.anyFalse() )
		return( mNumberOfCovered < mNumberOfElements );
	}

	/**
	 * set EXIT CODE
	 */
	inline void setExitCode() const
	{
		if( goalAchieved() )
		{
			avm_set_exit_code( AVM_EXIT_COVERAGE_GOAL_ACHIEVED_CODE);
		}
		else if( (mNumberOfElements > 0) &&
				(90 <= ((100 * mNumberOfCovered) / mNumberOfElements)) )
		{
			avm_set_exit_code( AVM_EXIT_COVERAGE_GOAL_ALMOST_ACHIEVED_CODE);
		}
		else
		{
			avm_set_exit_code( AVM_EXIT_COVERAGE_GOAL_UNACHIEVED_CODE);
		}
	}


	/**
	 * to string
	 */
	inline std::string strCoverageRate(const std::string & sep = " / ") const
	{
		return( OSS() << mNumberOfCovered << sep << mNumberOfElements );
	}

	inline std::string strCoverageRate(
			bool isGoalAchieved, const std::string & sep = " / ") const
	{
		return( OSS()
				<< (isGoalAchieved ? mNumberOfElements : mNumberOfCovered)
				<< sep << mNumberOfElements );
	}


	/**
	 * Serialization
	 */
	inline void toStreamCoverageRate(OutStream & os,
			const std::string & prompt = "", const std::string & sep = " / ",
			const std::string & eol = "\n") const
	{
		os << prompt << mNumberOfCovered << sep << mNumberOfElements
				<< eol << std::flush;
	}

	inline void toStreamFailedStep(OutStream & os,
			const std::string & prompt = "", const std::string & name = " / ",
			const std::string & eol = "\n") const
	{
		os << prompt << mNumberOfFailedStep << name
				<< ( (mNumberOfFailedStep > 0) ? "s" : "" )
				<< eol << std::flush;
	}

};


} /* namespace sep */

#endif /* AVMCOVERAGESTATISTICS_H_ */
