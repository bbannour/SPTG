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

#include <fml/executable/AvmTransition.h>

#include <fml/runtime/ExecutionContext.h>
#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/RuntimeID.h>

#include <fml/trace/TracePoint.h>

#include <fam/coverage/BaseCoverageFilter.h>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
// TRACE DRIVER API
////////////////////////////////////////////////////////////////////////////////

bool AvmCoverageTraceDriver::initialize(
		ExecutionContext * aDirectiveEC, AvmTransition * aTransition)
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

	RuntimeID aRID = mDirectiveEC->refExecutionData().getRuntimeID(
			mTransitionTarget->getExecutable() );

	TransitionReachability pathChecker(*mDirectiveEC, aRID, mTransitionTarget);

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
	ListOfExecutionContext::const_iterator ecQueueIt = aResultQueue.begin();
	ListOfExecutionContext::const_iterator ecQueueItEnd = aResultQueue.end();
	for( ; ecQueueIt != ecQueueItEnd ; ++ecQueueIt )
	{
		if( (*ecQueueIt) == mDirectiveEC )
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

	ExecutionContext::child_iterator itEC = mDirectiveEC->begin();
	ExecutionContext::child_iterator endEC = mDirectiveEC->end();

	avm_size_t coverageMax = 0;
	avm_size_t coverageCount = 0;

	BFList::const_iterator itTP;
	BFList::const_iterator endTP = mPendingTrace.points.end();

	for( ; itEC != endEC ; ++itEC )
	{
		coverageCount = 0;

		for( itTP = mPendingTrace.points.begin() ; itTP != endTP ; ++itTP )
		{
			if( mTraceChecker.isSatTransition(*(*itEC),
					(*itTP).to_ptr< TracePoint >(),
					(*itEC)->getRunnableElementTrace()) )
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

			mDirectiveEC = (*itEC);

			mDirectiveEC->setWeight( WEIGHT_STRONGLY_ACHIEVABLE );
		}
		else
		{
			(*itEC)->setWeight( WEIGHT_NON_PRIORITY );
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
		BaseCompiledForm::toStreamStaticCom(os,
				mTransitionTarget->getInternalCommunicationCode());
	}
	os << EOL_FLUSH;

	os << "Computed trace to reach it :> ";
	mDirectiveTrace.toStream(os);

	AVM_OS_COUT << "GOAL " << ( goalAchieved() ? "ACHIEVED" : "FAILED" )
			<< " !!!" << std::endl;
}



} /* namespace sep */
