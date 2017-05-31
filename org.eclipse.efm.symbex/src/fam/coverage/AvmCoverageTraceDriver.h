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

#ifndef AVMCOVERAGETRACEDRIVER_H_
#define AVMCOVERAGETRACEDRIVER_H_

#include <fam/coverage/AvmCoverageHeuristicProperty.h>

#include <collection/Typedef.h>

#include <fml/runtime/ExecutionContext.h>

#include <fml/trace/TraceChecker.h>
#include <fml/trace/TraceSequence.h>


namespace sep
{

class AvmTransition;
class EvaluationEnvironment;


class AvmCoverageTraceDriver :  public IHeuristicContextWeight
{

protected:
	EvaluationEnvironment & ENV;
	TraceChecker mTraceChecker;

	bool mInitializationFlag;
	AvmTransition * mTransitionTarget;
	ListOfAvmTransition mTransitionTargetHistory;

	ExecutionContext * mDirectiveEC;

	TraceSequence mDirectiveTrace;

	TraceSequence mPendingTrace;
	avm_size_t mPendingTraceSize;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmCoverageTraceDriver(EvaluationEnvironment & anENV)
	: IHeuristicContextWeight( ),
	ENV( anENV ),
	mTraceChecker( anENV ),
	mInitializationFlag( false ),
	mTransitionTarget( NULL ),
	mTransitionTargetHistory( ),

	mDirectiveEC( NULL ),
	mDirectiveTrace( ),
	mPendingTrace( ),
	mPendingTraceSize( 0 )
	{
		// TODO Auto-generated constructor stub

	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~AvmCoverageTraceDriver()
	{
		//!! NOTHING
	}

	/**
	 * GETTER
	 * mDirectiveEC
	 * mTransitionTargetHistory
	 */
	inline ExecutionContext * getDirectiveEC()
	{
		return( mDirectiveEC );
	}

	inline bool couldRetry()
	{
		return( mTransitionTargetHistory.nonempty() );
	}

	inline bool hasFailedTransitionTargetHistory()
	{
		return( mTransitionTargetHistory.nonempty() );
	}


	inline void resetFailedTransitionTargetHistory()
	{
		mTransitionTargetHistory.clear();
	}


	////////////////////////////////////////////////////////////////////////////
	// TRACE DRIVER API
	////////////////////////////////////////////////////////////////////////////

	bool initialize(ExecutionContext * aDirectiveEC, AvmTransition * aTransition);

	inline bool goalAchieved() const
	{
		return( mPendingTrace.points.empty() );
	}


	bool process(const ListOfExecutionContext & aResultQueue);

	bool drive();


	////////////////////////////////////////////////////////////////////////////
	// SERIALIZATION API
	////////////////////////////////////////////////////////////////////////////

	virtual void toStream(OutStream & os) const;


};


} /* namespace sep */

#endif /* AVMCOVERAGETRACEDRIVER_H_ */
