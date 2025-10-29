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

#include "AvmCoverageTraceDriver.h"

#include <builder/analysis/TransitionReachability.h>
#include <famcore/api/BaseCoverageFilter.h>

#include <fml/common/ObjectElement.h>

#include <fml/executable/AvmTransition.h>

#include <fml/runtime/ExecutionContext.h>
#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/RuntimeID.h>

#include <fml/trace/TracePoint.h>



namespace sep
{


////////////////////////////////////////////////////////////////////////////////
// TRACE DRIVER API
////////////////////////////////////////////////////////////////////////////////

bool AvmCoverageTraceDriver::initialize(
		ExecutionContext * aDirectiveEC, const AvmTransition * aTransition)
{
	if( mTransitionTargetHistory.contains( aTransition ) )
	{
		return( false );
	}

	mTransitionTargetHistory.push_front( aTransition );

	mTransitionTarget = aTransition;
	mDirectiveEC = aDirectiveEC;

	mDirectiveTrace.points.clear();
	mPendingTrace.points.clear();

	RuntimeID aRID = mDirectiveEC->getExecutionData().getRuntimeID(
			mTransitionTarget->refExecutable() );

	TransitionReachability pathChecker(*mDirectiveEC, aRID, (* mTransitionTarget));

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_COUT << std::endl << REPEAT("<<<<<<<<<<", 10) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )

	if( (mInitializationFlag = pathChecker.computePath(mDirectiveTrace)) )
	{
		mPendingTrace.copyTrace( mDirectiveTrace );

		mPendingTraceSize = mPendingTrace.points.size();

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	pathChecker.report(AVM_OS_COUT);
	AVM_OS_COUT << REPEAT(">>>>>>>>>>", 10) << std::endl << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	}

	return( mInitializationFlag );
}


bool AvmCoverageTraceDriver::process(const ListOfExecutionContext & aResultQueue)
{
	for( const auto & itQueueEC : aResultQueue )
	{
		if( itQueueEC == mDirectiveEC )
		{
			return( drive() );
		}
	}

	return( false );
}


bool AvmCoverageTraceDriver::drive()
{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_COUT << std::endl << REPEAT("==========", 10) << std::endl;
	AVM_OS_COUT << "Directive Trace:>" << std::endl;
	mPendingTrace.toStream(AVM_OS_COUT);
	AVM_OS_COUT << "Directive EC:> " << mDirectiveEC->str_min() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )

	std::size_t coverageMax = 0;
	std::size_t coverageCount = 0;

	for( const auto & itChildEC : mDirectiveEC->getChildContexts() )
	{
		coverageCount = 0;

		for( const auto & itPoint : mPendingTrace.points )
		{
			if( mTraceChecker.isSatTransition(*itChildEC,
					itPoint.to< TracePoint >(),
					itChildEC->getRunnableElementTrace()) )
			{
				++coverageCount;
			}
			else
			{
				break;
			}
		}

		if( coverageCount > coverageMax )
		{
			coverageMax = coverageCount;

			mDirectiveEC = itChildEC;

			mDirectiveEC->setWeight( WEIGHT_STRONGLY_ACHIEVABLE );
		}
		else
		{
			itChildEC->setWeight( WEIGHT_NON_PRIORITY );
		}
	}

	if( coverageMax > 0 )
	{
		if( coverageMax < mPendingTraceSize )
		{
			for( coverageCount = 0 ; coverageCount < coverageMax ; ++coverageCount )
			{
				mPendingTrace.points.pop_front();
			}
			mPendingTraceSize = mPendingTraceSize - coverageMax;

			mDirectiveEC->setWeight( WEIGHT_CERTAINLY_ACHIEVABLE );

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_COUT << "HIT ! EC:> "; mDirectiveEC->traceDefault(AVM_OS_COUT);
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
		}
		else
		{
			mTransitionTargetHistory.pop_front();

			mPendingTrace.points.clear();
			mPendingTraceSize = 0;

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_COUT << "GOAL ACHIEVED !!!" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
		}

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_COUT << REPEAT("==========", 10) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )

		return( true );
	}

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_COUT << REPEAT("==========", 10) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	return( false );
}


////////////////////////////////////////////////////////////////////////////////
// SERIALIZATION API
////////////////////////////////////////////////////////////////////////////////

void AvmCoverageTraceDriver::toStream(OutStream & os) const
{
	os << "Transition to reach :> ";
	mTransitionTarget->toStreamHeader(os);
	if( mTransitionTarget->hasInternalCommunicationCode() )
	{
		os << " ";
		ObjectElement::toStreamStaticCom(os,
				mTransitionTarget->getInternalCommunicationCode());
	}
	os << EOL_FLUSH;

	os << "Computed trace to reach it :> ";
	mDirectiveTrace.toStream(os);

	AVM_OS_COUT << "GOAL " << ( goalAchieved() ? "ACHIEVED" : "FAILED" )
			<< " !!!" << std::endl;
}



} /* namespace sep */
