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

#ifndef BASEHITPROCESSOR_H_
#define BASEHITPROCESSOR_H_

#include <collection/BFContainer.h>
#include <famcore/api/BaseCoverageFilter.h>

#include <fml/executable/ExecutableForm.h>

#include <fml/runtime/ExecutionContext.h>

#include <fml/trace/TraceChecker.h>

#include <solver/api/SolverDef.h>



namespace sep
{

class BF;

class AvmCode;
class AvmCoverageStatistics;
class AvmHitOrJumpProcessor;

class EvaluationEnvironment;
class ExecutionContext;
class ExecutableSystem;

class Operator;


class BaseHitProcessor
{


protected:
	/**
	 * ATTRIBUTE
	 */
	AvmHitOrJumpProcessor & mHitOrJumpProcessor;

	AvmCoverageStatistics & mCoverageStatistics;

	EvaluationEnvironment & ENV;

	SolverDef::SOLVER_KIND mSolverKind;

	ExecutableForm mLocalExecutableForm;

	TraceChecker mTraceChecker;

	AvmCode mTraceObjective;
	bool isPureStateTransitionNatureFlag;

	// Computing Local Variables
	std::size_t traceOffset;

	ListOfExecutionContext & mRelativeRootEC;

	ListOfExecutionContext::iterator ecIt;
	ListOfExecutionContext::iterator ecItEnd;

	VectorOfExecutionContext & mRelativeLeafEC;

	ListOfExecutionContext & mAbsoluteLeafEC;
	ListOfExecutionContext & mBlackHoleEC;

	ListOfExecutionContext & mBacktrackHitEC;
	bool mBacktrackFlag;

	std::size_t mJumpHeight;

	VectorOfExecutionContext mMaxHitEC;
	std::size_t hitOffset;
	std::size_t hitOffsetEnd;

	std::size_t mMaxHitCount;

	ExecutionContext::child_iterator ecChildIt;
	ExecutionContext::child_iterator ecChildItEnd;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BaseHitProcessor(AvmHitOrJumpProcessor & hojProcessor,
			EvaluationEnvironment & anENV, const Operator * op);

	/**
	 * DESTRUCTOR
	 */
	virtual ~BaseHitProcessor()
	{
		//!! NOTHING
	}


	virtual std::string strKind() = 0;

	/**
	 * GETTER
	 * mTraceObjective
	 */
	bool isPureStateTransitionObjective() const;


	/**
	 * Coverage Test
	 */
	inline bool goalAchieved()
	{
		return( mCoverageStatistics.goalAchieved() );
	}

	inline bool hasUncovered()
	{
		return( mCoverageStatistics.hasUncovered() );
	}


	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE API
	////////////////////////////////////////////////////////////////////////////

	virtual bool configure(const WObject * wfParameterObject);

	virtual bool resetConfig();


	////////////////////////////////////////////////////////////////////////////
	// HIT FILTERING API
	////////////////////////////////////////////////////////////////////////////

	virtual bool goalWillNeverAchieved(ExecutionContext & anEC) = 0;

	virtual bool hit(std::size_t jumpHeight) = 0;

	virtual void hitSelect(std::size_t jumpOffset) = 0;


	inline bool hit(ExecutionContext & anEC, const BF & arg)
	{
		return( mTraceChecker.isSat(anEC, arg) );
	}

	// FILTERING TOOLS
	bool isAbsoluteLeaf(ExecutionContext & anEC);


	////////////////////////////////////////////////////////////////////////////
	// WILL NEVER HIT FILTERING API
	////////////////////////////////////////////////////////////////////////////

	inline bool willNeverHit(ExecutionContext & anEC, const BF & arg)
	{
		++mCoverageStatistics.mNumberOfBlackHoleTest;

		return( mTraceChecker.willNeverSat(anEC, arg) );
	}


	////////////////////////////////////////////////////////////////////////////
	// REPORT API
	////////////////////////////////////////////////////////////////////////////

	inline void reportMinimum(OutStream & os) const
	{
		if( mCoverageStatistics.hasUncovered() )
		{
			toStreamUncovered(os);
		}
		toStreamCovered(os);
	}


	inline void reportDefault(OutStream & os) const
	{
		if( mCoverageStatistics.hasUncovered() )
		{
			toStreamUncovered(os);
		}

		if( mCoverageStatistics.hasCovered() )
		{
			toStreamCovered(os);
		}
	}



	////////////////////////////////////////////////////////////////////////////
	// SERIALIZATION API
	////////////////////////////////////////////////////////////////////////////

	void toStreamCovered(OutStream & os) const;

	void toStreamUncovered(OutStream & os) const;

	inline virtual void toStream(OutStream & os) const
	{
		toStreamUncovered(os);

		toStreamCovered(os);
	}

};


} /* namespace sep */

#endif /* BASEHITPROCESSOR_H_ */
