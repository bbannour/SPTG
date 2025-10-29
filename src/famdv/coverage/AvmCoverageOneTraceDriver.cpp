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

#include "AvmCoverageOneTraceDriver.h"

#include "AvmCoverageProcessor.h"
#include "AvmCoverageTransitionView.h"

#include <fml/common/ObjectElement.h>

#include <fml/executable/AvmTransition.h>

#include <fml/runtime/ExecutionContext.h>
#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/RuntimeID.h>

#include <fml/trace/TracePoint.h>

#include  <famdv/coverage/AvmCoverageTransitionView.h>

#include  <famcore/queue/WaitingStrategy.h>

#include <sew/SymbexControllerRequestManager.h>

#include <functional>


namespace sep
{


/**
 * CONSTRUCTOR
 * Default
 */
AvmCoverageOneTraceDriver::AvmCoverageOneTraceDriver(
		AvmCoverageProcessor & aCoverageProcessor, EvaluationEnvironment & anENV,
		IHeuristicClass::ENUM_HEURISTIC_CLASS anHeuristicClass,
		std::size_t pathCountLimit, std::size_t pathSizeLimit)
: AvmCoverageAbstractView( aCoverageProcessor , nullptr ),
mTransitionCoverage( aCoverageProcessor.mTransitionCoverage ),
ENV( anENV ),
mTraceChecker( anENV ),

mComputingPathCountLimit( pathCountLimit ),
mComputingPathSizeLimit( pathSizeLimit ),
mPathChecker(anHeuristicClass, pathCountLimit, pathSizeLimit),

mTransitionTargetHistory( ),

mCacheForDirectiveTraces( ),
mDirectiveEC( nullptr ),

mDefaultPendingTraceSize( 4 ),

mPendingTrace( & aCoverageProcessor.mTransitionCoverage ),

mWaitingQueue( ),

mGlobalUncoveredTransitions( ),
mLastCollectedCoverCount( 0 ),

mLocalUncoveredTransitions( ),

// Computing drive variable
saveWeightMin( 0 ),

coverageMax( 0 ),
coverageCount( 0 ),

tmpTracePoint( nullptr ),
itTP( ),
endTP( ),

tmpTransition( nullptr ),
itTransition( ),
endTransition( ),

itTrace( ),
endTrace( )
{
	// TODO Auto-generated constructor stub

}


////////////////////////////////////////////////////////////////////////////////
// CONFIGURE API
////////////////////////////////////////////////////////////////////////////////

bool AvmCoverageOneTraceDriver::configureImpl()
{
	return( true );
}


////////////////////////////////////////////////////////////////////////////////
// PROCESSOR FILTER API
////////////////////////////////////////////////////////////////////////////////

bool AvmCoverageOneTraceDriver::prefiltering(ListOfExecutionContext & ecQueue)
{
//	endQueue = ecQueue.end();
//	for( itQueue = ecQueue.begin() ; itQueue != endQueue ; ++itQueue )
//	{
//
//	}

	return( true );
}

bool AvmCoverageOneTraceDriver::postfiltering(ListOfExecutionContext & ecQueue)
{
	itQueue = ecQueue.begin();
	endQueue = ecQueue.end();
	for( ; itQueue != endQueue ; ++itQueue )
	{
		if( (*itQueue) == mDirectiveEC )
		{
			if( drive() )
			{
				return( true );
			}
		}
	}

	mCoverageProcessor.setRequestRequeueWaiting();

	return( false );
}



////////////////////////////////////////////////////////////////////////////////
// PROCESSOR REQUEST API
////////////////////////////////////////////////////////////////////////////////
/**
 * REQUEUE_WAITING
 */
bool AvmCoverageOneTraceDriver::requeueWaitingTable(
		WaitingStrategy & aWaitingStrategy,
		std::uint8_t aWeightMin, std::uint8_t aWeightMax)
{
	// Global Update Cache for Directive Traces !!!
	updateCacheForDirectiveTraces();


	mWaitingQueue.clear();

	saveWeightMin = aWeightMin;

	aWeightMin = aWaitingStrategy.flushPriorQueueTable(
			mWaitingQueue, saveWeightMin, aWeightMax);

//	while( aWeightMin <= WEIGHT_WEAKLY_ACHIEVABLE )
	while( aWeightMin <= WEIGHT_NON_PRIORITY )
	{
		itQueue = mWaitingQueue.begin();
		endQueue = mWaitingQueue.end();
		for( ; itQueue != endQueue ; ++itQueue )
		{
			if( checkDirectiveTrace(* (*itQueue)) )
			{
				(*itQueue)->setWeight( WEIGHT_SELECTED_ACHIEVABLE );

				aWaitingStrategy.push( *itQueue );

				itQueue = mWaitingQueue.erase( itQueue );

				aWaitingStrategy.splice(aWeightMin, mWaitingQueue);

				return( setDirectiveTrace() );
			}
		}

		aWaitingStrategy.splice(aWeightMin, mWaitingQueue);

		aWeightMin = aWaitingStrategy.flushPriorQueueTable(
				mWaitingQueue, ++aWeightMin, aWeightMax);
	}

	aWaitingStrategy.splice(aWeightMin, mWaitingQueue);


	if( mGlobalUncoveredTransitions.empty() )
	{
		mLastCollectedCoverCount = mCoverageStatistics.mNumberOfCovered;

		mTransitionCoverage.collectUncoveredTransition(
				mGlobalUncoveredTransitions);
	}
	else if( mLastCollectedCoverCount < mCoverageStatistics.mNumberOfCovered )
	{
		mLastCollectedCoverCount = mCoverageStatistics.mNumberOfCovered;

		mTransitionCoverage.updateUncoveredTransition(
				mGlobalUncoveredTransitions);
	}


	aWeightMin = aWaitingStrategy.flushPriorQueueTable(
			mWaitingQueue, saveWeightMin, aWeightMax);

	while( aWeightMin <= WEIGHT_UNKNOWN_ACHIEVABLE )
	{
		itQueue = mWaitingQueue.begin();
		endQueue = mWaitingQueue.end();
		for( ; itQueue != endQueue ; ++itQueue )
		{
			if( checkDirectiveTrace(*(*itQueue), mGlobalUncoveredTransitions) )
			{
				(*itQueue)->setWeight( WEIGHT_SELECTED_ACHIEVABLE );

				aWaitingStrategy.push( *itQueue );

				itQueue = mWaitingQueue.erase( itQueue );

				aWaitingStrategy.splice(aWeightMin, mWaitingQueue);

				return( setDirectiveTrace() );
			}
		}

		aWaitingStrategy.splice(aWeightMin, mWaitingQueue);

		aWeightMin = aWaitingStrategy.flushPriorQueueTable(
				mWaitingQueue, ++aWeightMin, aWeightMax);
	}

	aWaitingStrategy.splice(aWeightMin, mWaitingQueue);

	if( selectDirectiveTrace() )
	{
		aWaitingStrategy.remove( mDirectiveEC );

		mDirectiveEC->setWeight( WEIGHT_SELECTED_ACHIEVABLE );

		aWaitingStrategy.push( mDirectiveEC );

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
		AVM_OS_TRACE << "selectDirectiveTrace :> ";
		mDirectiveEC->traceMinimum(AVM_OS_TRACE);
		aWaitingStrategy.toStream(AVM_OS_TRACE);
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )

		resetFailedTransitionTargetHistory();

		return( setDirectiveTrace() );
	}

	resetFailedTransitionTargetHistory();

	mCoverageProcessor.setRequestHeuristic();

	return( false );
}


////////////////////////////////////////////////////////////////////////////////
// TRACE DRIVER API
////////////////////////////////////////////////////////////////////////////////

/**
 * UPDATE
 * mCacheForDirectiveTraces
 */
void AvmCoverageOneTraceDriver::appendDirectiveTraces(AvmTraceProperty & aTrace)
{
	if( mCacheForDirectiveTraces.empty() )
	{
		mCacheForDirectiveTraces.push_back( aTrace );
	}
//	else if( aTrace.isInf( std::less<std::size_t>(),
//			mCacheForDirectiveTraces.front() ) )
	else if( aTrace.sizeLT( mCacheForDirectiveTraces.front() ) )
	{
		mCacheForDirectiveTraces.push_front( aTrace );
	}
	else if( aTrace.sizeGT( mCacheForDirectiveTraces.back() ) )
	{
		mCacheForDirectiveTraces.push_back( aTrace );
	}
	else
	{
		itTrace = mCacheForDirectiveTraces.begin();
		endTrace = mCacheForDirectiveTraces.end();
		for( ; itTrace != endTrace ; ++itTrace )
		{
			if( aTrace.sizeLT( *itTrace ) )
			{
				break;
			}
		}
		mCacheForDirectiveTraces.insert(itTrace, aTrace);
	}
}


bool AvmCoverageOneTraceDriver::checkDirectiveContext(
		const ExecutionContext & aDirectiveEC,
		const AvmTransition * aTransition)
{
	itTrace = mCacheForDirectiveTraces.begin();
	endTrace = mCacheForDirectiveTraces.end();
	for( ; itTrace != endTrace ; ++itTrace )
	{
		if( ((& aDirectiveEC) == (*itTrace).mEC) &&
			(aTransition  == (*itTrace).backTransition()) )
		{
			return( true );
		}
	}

	return( false );
}


bool AvmCoverageOneTraceDriver::computeDirectiveTrace(
		const ExecutionContext & aDirectiveEC,
		const AvmTransition * aTransition)
{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
	AVM_OS_TRACE << TAB << "AvmCoverageTraceDriver :>" << AVM_STR_INDENT;
	aDirectiveEC.traceMinimum(AVM_OS_TRACE);
	AVM_OS_TRACE << END_INDENT;
	AVM_OS_TRACE << " |= " ; aTransition->toStreamHeader(AVM_OS_TRACE);
	AVM_OS_TRACE << std::endl;// << INCR_INDENT;
//	AvmTransition::toStream(AVM_OS_TRACE, mTransitionTargetHistory);
//	AVM_OS_TRACE << DECR_INDENT;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )

//	if( mTransitionTargetHistory.contains(aTransition) )
//	{
//		return( false );
//	}
//	else
		if( checkDirectiveContext(aDirectiveEC, aTransition) )
	{
		return( false );
	}
	else
	{
		mPendingTrace.clear();

		mDirectiveEC = const_cast< ExecutionContext *>( & aDirectiveEC );

		RuntimeID aRID = aDirectiveEC.getExecutionData().getRuntimeID(
				aTransition->refExecutable() );

		if( mPathChecker.computePath(mPendingTrace,
				mDirectiveEC, aRID, aTransition,
				mHeuristicProperty.mDirectiveTraceHeuristicClass,
				mHeuristicProperty.mDirectiveTraceCountLimit,
				mHeuristicProperty.mDirectiveTraceSizeLimit) )
		{
			mPendingTrace.mEC = (& aDirectiveEC);

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	mPathChecker.report(AVM_OS_COUT);
	mPathChecker.report(AVM_OS_TRACE);
	AVM_OS_TRACE << REPEAT(">>>>>>>>>>", 10) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )

			return( true );
		}

		return( false );
	}
}


bool AvmCoverageOneTraceDriver::selectDirectiveTrace()
{
	if( mCacheForDirectiveTraces.nonempty() )
	{
		toStreamCache( AVM_OS_TRACE , "selectDirectiveTrace"  );

		mPendingTrace.clear();
		mPendingTrace.copyTrace( mCacheForDirectiveTraces.front() );

		mDirectiveEC = const_cast< ExecutionContext * >( mPendingTrace.mEC );

		mCacheForDirectiveTraces.pop_front();

		return( true );
	}

	return( false );
}

bool AvmCoverageOneTraceDriver::setDirectiveTrace()
{
	mTransitionTargetHistory.push_front( mPendingTrace.backTransition() );

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_TRACE << std::endl << REPEAT("++++++++++", 10) << std::endl;
	AVM_OS_TRACE << "ObjectiveTrace:> " << mDirectiveEC->str_min() << std::endl;
	mPendingTrace.toStream(AVM_OS_TRACE, true);
	AVM_OS_TRACE << REPEAT("++++++++++", 10) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )

	return( true );
}




bool AvmCoverageOneTraceDriver::updateCacheForDirectiveTraces(
		const ExecutionContext & anEC)
{
	bool isUpdated = false;

	if( //(mLastCollectedCoverCount == mCoverageStatistics.mNumberOfCovered) ||
			mCacheForDirectiveTraces.empty() )
	{
		return( isUpdated );
	}

	endTrace = mCacheForDirectiveTraces.end();
	for( itTrace = mCacheForDirectiveTraces.begin() ; itTrace != endTrace ; )
	{
		if( (*itTrace).mEC == (& anEC) )
		{
			isUpdated = true;

			itTrace = mCacheForDirectiveTraces.erase( itTrace );
		}
		else
		{
			++itTrace;
		}
	}

	return( isUpdated );
}


bool AvmCoverageOneTraceDriver::updateCacheForDirectiveTraces(
		AvmTransition * aTransition)
{
	bool isUpdated = false;

	mTransitionTargetHistory.remove( aTransition );

	if( //(mLastCollectedCoverCount == mCoverageStatistics.mNumberOfCovered) ||
			mCacheForDirectiveTraces.empty() )
	{
		return( isUpdated );
	}

	endTrace = mCacheForDirectiveTraces.end();
	for( itTrace = mCacheForDirectiveTraces.begin() ; itTrace != endTrace ; )
	{
		tmpTransition = (*itTrace).backTransition();

		if( tmpTransition == aTransition )
		{
			isUpdated = true;

			itTrace = mCacheForDirectiveTraces.erase( itTrace );
		}
		else
		{
			++itTrace;
		}
	}

	return( isUpdated );
}


bool AvmCoverageOneTraceDriver::updateCacheForDirectiveTraces()
{
//	mCacheForDirectiveTraces.clear();

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_TRACE << "updateCacheForDirectiveTraces:> size: "
			<< mCacheForDirectiveTraces.size() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )

	updateTransitionTargetHistory();

	bool isUpdated = false;

	if( //(mLastCollectedCoverCount == mCoverageStatistics.mNumberOfCovered) ||
			mCacheForDirectiveTraces.empty() )
	{
		return( isUpdated );
	}

	endTrace = mCacheForDirectiveTraces.end();
	for( itTrace = mCacheForDirectiveTraces.begin() ; itTrace != endTrace ; )
	{
		tmpTransition = (*itTrace).backTransition();

		if( (*itTrace).mEC->hasNext() )
		{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
	AVM_OS_TRACE << "remove<EC>";
	(*itTrace).mEC->traceMinimum( AVM_OS_TRACE );
	AVM_OS_TRACE << "\ttransition:> " << tmpTransition->getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )

			isUpdated = true;

			itTrace = mCacheForDirectiveTraces.erase( itTrace );
		}
		else if( mTransitionCoverage.testTransitionCoverage( tmpTransition ) )
		{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
	AVM_OS_TRACE << "remove<transition> ";
	(*itTrace).mEC->traceMinimum( AVM_OS_TRACE );
	AVM_OS_TRACE << "\ttransition:> " << tmpTransition->getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )

			isUpdated = true;

			itTrace = mCacheForDirectiveTraces.erase( itTrace );

			mTransitionTargetHistory.remove( tmpTransition );
		}
		else
		{

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
	AVM_OS_TRACE << "preserve :> "; (*itTrace).mEC->traceMinimum( AVM_OS_TRACE );
	AVM_OS_TRACE << "\ttransition:> " << tmpTransition->getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )

			++itTrace;
		}
	}

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_TRACE << "updateCacheForDirectiveTraces:> size<update>: "
			<< mCacheForDirectiveTraces.size() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )

	return( isUpdated );
}


bool AvmCoverageOneTraceDriver::updateTransitionTargetHistory()
{
	bool isUpdated = false;

	ListOfAvmTransition::iterator itTransition = mTransitionTargetHistory.begin();
	ListOfAvmTransition::iterator endTransition = mTransitionTargetHistory.end();
	for( ; itTransition != endTransition ; )
	{
		if( mTransitionCoverage.testTransitionCoverage( *itTransition ) )
		{
			itTransition = mTransitionTargetHistory.erase( itTransition );

			isUpdated = true;
		}
		else
		{
			++itTransition;
		}
	}

	return( isUpdated );
}

/**
 * Compute a directive trace
 */
bool AvmCoverageOneTraceDriver::checkDirectiveTrace(
		const ExecutionContext & anEC)
{
	mLocalUncoveredTransitions.clear();

	mTransitionCoverage.collectUncoveredTransition(
			anEC.getExecutionData(), mLocalUncoveredTransitions);

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
	AVM_OS_TRACE << "checkDirectiveTrace:> local uncovered transitions count: "
			<< mLocalUncoveredTransitions.size() << std::endl;
	for( const auto & itTransition : mLocalUncoveredTransitions )
	{
		AVM_OS_TRACE << "\t" << itTransition->strTransitionHeader() << std::endl;
	}
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )

	return( checkDirectiveTrace(anEC, mLocalUncoveredTransitions) );
}


bool AvmCoverageOneTraceDriver::checkDirectiveTrace(
		const ExecutionContext & anEC,
		const VectorOfAvmTransition & tableofTransitions)
{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
	AVM_OS_TRACE << std::endl << REPEAT("<<<<<<<<<<", 10) << std::endl;
	AVM_OS_TRACE << "checkDirectiveTrace:> ";  anEC.traceMinimum(AVM_OS_TRACE);
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )

	itTransition = tableofTransitions.begin();
	endTransition = tableofTransitions.end();
	for( ; itTransition != endTransition ; ++itTransition )
	{
		if( computeDirectiveTrace(anEC, *itTransition) )
		{
			if( mPendingTrace.mSize < mDefaultPendingTraceSize )
			{
				return( true );
			}
			else
			{
				appendDirectiveTraces( mPendingTrace );
			}
		}
	}

	return( false );
}


bool AvmCoverageOneTraceDriver::drive()
{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_TRACE << std::endl << REPEAT("==========", 10) << std::endl;
	AVM_OS_TRACE << "DirectiveTrace:> " << mDirectiveEC->str_min() << std::endl;
	mPendingTrace.toStream(AVM_OS_TRACE, false);
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )

	coverageMax = 0;

	endTP = mPendingTrace.points.end();

	endEC = mDirectiveEC->end();
	for( itEC = mDirectiveEC->begin() ; itEC != endEC ; ++itEC )
	{
		coverageCount = 0;

		for( itTP = mPendingTrace.points.begin() ; itTP != endTP ; ++itTP )
		{
			tmpTracePoint = (*itTP).to_ptr< TracePoint >();

			if( mTraceChecker.isSatTransition(*(*itEC),
					tmpTracePoint, (*itEC)->getRunnableElementTrace()) )
			{
				++coverageCount;
			}
			else
			{
				if( (coverageCount > 0) && tmpTracePoint->object->
						as< AvmTransition >().isUnstableSource() )
				{
					coverageCount = 0;
				}

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
			mTransitionCoverage.computeWeight( *itEC );

//			(*itEC)->setWeight( WEIGHT_NON_PRIORITY );
		}
	}

	if( coverageMax > 0 )
	{
		if( coverageMax < mPendingTrace.mSize )
		{
			mPendingTrace.pop_front( coverageMax );

			mDirectiveEC->setWeight( WEIGHT_SELECTED_ACHIEVABLE );

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_TRACE << "HIT ! EC:> "; mDirectiveEC->traceMinimum(AVM_OS_TRACE);
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
		}
		else
		{
			mTransitionTargetHistory.pop_front();

			mPendingTrace.clear();

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_TRACE << "GOAL ACHIEVED !!!" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
		}

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_TRACE << REPEAT("==========", 10) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )

		return( true );
	}
	else
	{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_TRACE << "GOAL FAILED !!!" << std::endl;
	AVM_OS_TRACE << REPEAT("==========", 10) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )

		return( false );
	}
}


////////////////////////////////////////////////////////////////////////////////
// SERIALIZATION API
////////////////////////////////////////////////////////////////////////////////

void AvmCoverageOneTraceDriver::toStream(OutStream & os) const
{
	os << "Transition to reach :> ";

	const AvmTransition * aTransition = mPendingTrace.backTransition();

	aTransition->toStreamHeader(os);
	if( aTransition->hasInternalCommunicationCode() )
	{
		os << " ";
		ObjectElement::toStreamStaticCom(os,
				aTransition->getInternalCommunicationCode());
	}
	os << EOL_FLUSH;

	os << "Computed trace to reach it :> ";
	mPendingTrace.toStream(os, false);

	AVM_OS_TRACE << "GOAL " << ( goalAchieved() ? "ACHIEVED" : "FAILED" )
			<< " !!!" << std::endl;
}


void AvmCoverageOneTraceDriver::toStreamCache(
		OutStream & os, const std::string strMessage) const
{
	os << TAB << strMessage << "<size: " << mCacheForDirectiveTraces.size()
			<< "> {" << EOL_INCR_INDENT;

	ListOfAvmTraceProperty::const_iterator itTrace =
			mCacheForDirectiveTraces.begin();
	ListOfAvmTraceProperty::const_iterator endTrace =
			mCacheForDirectiveTraces.end();
	for( ; itTrace != endTrace ; ++itTrace )
	{
		(*itTrace).toStream(os, false);
	}

	os << TAB << "mTransitionTargetHistory<size: "
			<< mTransitionTargetHistory.size() << ">" << EOL;
	AvmTransition::toStream(os, mTransitionTargetHistory);

	os << DECR_INDENT_TAB << "}" << EOL_FLUSH;
}





} /* namespace sep */
