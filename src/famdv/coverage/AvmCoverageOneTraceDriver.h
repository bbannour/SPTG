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

#ifndef AVMCOVERAGEONETRACEDRIVER_H_
#define AVMCOVERAGEONETRACEDRIVER_H_

#include "AvmCoverageAbstractView.h"

#include <fml/runtime/ExecutionContext.h>

#include <fml/trace/TraceChecker.h>

#include  <famdv/coverage/AvmCoverageDirectiveTraceBuilder.h>


namespace sep
{

class WaitingStrategy;
class AvmTransition;
class AvmCoverageTransitionView;
class EvaluationEnvironment;


class AvmCoverageOneTraceDriver  :  public AvmCoverageAbstractView
{

	AVM_DECLARE_CLONABLE_CLASS( AvmCoverageOneTraceDriver )


protected:
	/**
	 * TYPEDEF
	 */
	typedef Vector < const AvmTransition * >  VectorOfAvmTransition;

	typedef List   < const AvmTransition * > ListOfAvmTransition;

	/**
	 * ATTRINUTES
	 */
	AvmCoverageTransitionView & mTransitionCoverage;

	EvaluationEnvironment & ENV;
	TraceChecker mTraceChecker;

	std::size_t mComputingPathCountLimit;
	std::size_t mComputingPathSizeLimit;
	AvmCoverageDirectiveTraceBuilder mPathChecker;

	ListOfAvmTransition mTransitionTargetHistory;

	ListOfAvmTraceProperty mCacheForDirectiveTraces;

	ExecutionContext * mDirectiveEC;

	std::size_t mDefaultPendingTraceSize;

	AvmTraceProperty mPendingTrace;

	ListOfExecutionContext mWaitingQueue;

	VectorOfAvmTransition mGlobalUncoveredTransitions;
	std::size_t mLastCollectedCoverCount;

	VectorOfAvmTransition mLocalUncoveredTransitions;

	// Computing drive variable
	std::uint8_t saveWeightMin;

	std::size_t coverageMax;
	std::size_t coverageCount;

	const TracePoint * tmpTracePoint;
	BFList::const_iterator itTP;
	BFList::const_iterator endTP;

	const AvmTransition * tmpTransition;
	VectorOfAvmTransition::const_iterator itTransition;
	VectorOfAvmTransition::const_iterator endTransition;

	ListOfAvmTraceProperty::iterator itTrace;
	ListOfAvmTraceProperty::iterator endTrace;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmCoverageOneTraceDriver(AvmCoverageProcessor & aCoverageProcessor,
			EvaluationEnvironment & anENV,
			IHeuristicClass::ENUM_HEURISTIC_CLASS
					anHeuristicClass = IHeuristicClass::HEURISTIC_SMART_CLASS,
			std::size_t pathCountLimit = 8, std::size_t pathSizeLimit = 8);

	/**
	 * DESTRUCTOR
	 */
	virtual ~AvmCoverageOneTraceDriver()
	{
		//!! NOTHING
	}


	/**
	 * GETTER
	 * mTransitionTargetHistory
	 */
	inline bool couldRetry() const
	{
		return( mTransitionTargetHistory.nonempty() );
	}

	inline bool hasFailedTransitionTargetHistory()const
	{
		return( mTransitionTargetHistory.nonempty() );
	}


	inline void resetFailedTransitionTargetHistory()
	{
		mTransitionTargetHistory.clear();
	}


	/**
	 * UPDATE
	 * mCacheForDirectiveTraces
	 */
	void appendDirectiveTraces(AvmTraceProperty & aTrace);

	bool checkDirectiveContext(const ExecutionContext & aDirectiveEC);

	bool checkDirectiveContext(
			const ExecutionContext & aDirectiveEC,
			const AvmTransition * aTransition);

	bool computeDirectiveTrace(
			const ExecutionContext & aDirectiveEC,
			const AvmTransition * aTransition);

	bool selectDirectiveTrace();
	bool setDirectiveTrace();

	bool updateCacheForDirectiveTraces(const ExecutionContext & anEC);

	bool updateCacheForDirectiveTraces(AvmTransition * aTransition);

	bool updateCacheForDirectiveTraces();

	bool updateTransitionTargetHistory();


	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	// COVERAGE PROCESSOR API
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////

	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE API
	////////////////////////////////////////////////////////////////////////////

	inline virtual bool configure() override
	{
		return( true );
	}

	virtual bool configureImpl() override;


	////////////////////////////////////////////////////////////////////////////
	// PROCESS API
	////////////////////////////////////////////////////////////////////////////


	////////////////////////////////////////////////////////////////////////////
	// FILTER API
	////////////////////////////////////////////////////////////////////////////

	bool prefiltering(ListOfExecutionContext & ecQueue);

	bool postfiltering(ListOfExecutionContext & ecQueue);

	////////////////////////////////////////////////////////////////////////////
	// PROCESSOR REQUEST API
	////////////////////////////////////////////////////////////////////////////
	/**
	 * REQUEUE_WAITING
	 */
	bool requeueWaitingTable(WaitingStrategy & aWaitingStrategy,
			std::uint8_t aWeightMin, std::uint8_t aWeightMax);


	////////////////////////////////////////////////////////////////////////////
	// TRACE DRIVER API
	////////////////////////////////////////////////////////////////////////////

	bool checkDirectiveTrace(const ExecutionContext & anEC);

	bool checkDirectiveTrace(const ExecutionContext & anEC,
			const VectorOfAvmTransition & tableofTransitions);

	inline bool goalAchieved() const
	{
		return( mPendingTrace.empty() );
	}

	bool drive();


	////////////////////////////////////////////////////////////////////////////
	// SERIALIZATION API
	////////////////////////////////////////////////////////////////////////////

	virtual void toStream(OutStream & os) const override;

	virtual void toStreamCache(OutStream & os,
			const std::string strMessage = "The Directive Trace Cache") const;


};


} /* namespace sep */

#endif /* AVMCOVERAGEONETRACEDRIVER_H_ */
