/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/
#include "ExecutionQueue.h"

#include "WaitingBasicStrategy.h"
#include "WaitingStrategyBLOCK.h"
#include "WaitingStrategyWEIGHT.h"

#include <fam/api/MainProcessorUnit.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <sew/SymbexDispatcher.h>
#include <sew/Workflow.h>

namespace sep
{


/**
 * DESTRUCTOR
 */
ExecutionQueue::~ExecutionQueue()
{
	// Unregistration
	getSymbexDispatcher().getSymbexEventManager().
			unregisterHandlerEventDestroyCtx(this);
}



/**
 *******************************************************************************
prototype execution_queue as avm::core.EXECUTION_QUEUE is
	section PROPERTY
		// 'ALL'

		// 'BEST'  | 'BEST_FIRST_SEARCH'
		// 'BFS'   | 'BREADTH_FIRST_SEARCH'
		// 'DFS'   | 'DEPTH_FIRST_SEARCH'
		// 'RFS'   | 'RANDOM_FIRST_SEARCH'
		// 'XFS'   | 'RANDOM_FIRST_SEARCH'

		// 'FIRST' | 'LAST'

		// 'BLOCK_{ ALL | BEST | BFS | DFS | RFS | XFS }'

		// 'WEIGHT_{ ALL | BEST | BFS | DFS | RFS | XFS }'

		// 'TARGET_FORMULA_{ ALL | BEST | BFS | DFS | RFS | XFS }'

		@strategy = 'BFS';

		// for WEIGHT_{ ALL | BEST | BFS | DFS | RFS | XFS } strategy
		@weight = 8;

		// for 'BLOCK_{ ALL | BEST | BFS | DFS | RFS | XFS }'
		// local block height and width size
		@block_height = 20;
		@block_width  = 30;

		// next height and width limit ==> pour éviter toute explosion localisée
		@height = 50;
		@width  = 30;
	endsection PROPERTY
endprototype
 *******************************************************************************
 */

/*
 * NEW CONSISE SYNTAX
supervisor {
	limit 'of graph exploration' [
		eval = 10
		...
	]
	queue 'for graph exploration' [
		strategy = 'BFS'
		...
	]
	// shortcut alternative
	queue = 'BFS'

	console [
		format = "\nstep:%1% , context:%2% , height:%3% , width:%4%"
		...
	]
}
*/

/**
 * CONFIGURE
 */
bool ExecutionQueue::configureImpl()
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mParameterWObject )
			<< "ExecutionQueue WObject !!!"
			<< SEND_EXIT;

	// INITIALIZATION
	configureDebug();

	// See ProcessorUnitFactory.cpp --> // QUEUE PROCESSOR CONFIGURE
	mConfigFlag = true;

	bool isnotDefinedWTypedObjectParameters = false;

	WObject * wfQueue = mParameterWObject;

	if( MainProcessorUnit::AUTO_REGISTER_TOOL.isTypeID( *mParameterWObject ) )
	{
		wfQueue = Query::getRegexWObjectByNameID(mParameterWObject,
				PREFIX_WID("symbex", OR_WID2("queue" , "QUEUE")),
						WObject::_NULL_);

		if( wfQueue == WObject::_NULL_ )
		{
			return( mConfigFlag );
		}
		else if( wfQueue->isWTypedOrReference() )
		{
			if( wfQueue->isWPropertyWReference() )
			{
				wfQueue = wfQueue->getWReferenceValue();
			}

			if( ExecutionQueue::AUTO_REGISTER_TOOL.isTypeID( *wfQueue ) )
			{
				mParameterWObject = wfQueue;
			}
			else
			{
				AVM_OS_WARN << "ExecutionQueue::configure:> "
						"Unexpected the WObject< "
						<< wfQueue->getFullyQualifiedNameID()
						<< " > as queue parameters defined in supervisor <"
						<< mParameterWObject->getFullyQualifiedNameID()
						<< " >! " << std::endl;

				return( mConfigFlag = false );
			}
		}
		else if( wfQueue->isWSequence() )
		{
			// case supervisor sequence parameters

			isnotDefinedWTypedObjectParameters = true;
		}
		else if( wfQueue->isWPropertyString() )
		{
			// case supervisor single shortcut property parameter

			isnotDefinedWTypedObjectParameters = true;
		}
		else
		{
			AVM_OS_WARN << "ExecutionQueue::configure:> "
					"Unexpected the WObject< " << wfQueue->strHeader()
					<< " > as redundancy parameters defined in supervisor <"
					<< mParameterWObject->getFullyQualifiedNameID()
					<< " >! " << std::endl;

			return( mConfigFlag = false );
		}
	}

	WObject * theQUEUE = ( isnotDefinedWTypedObjectParameters ) ?  wfQueue
			: Query::getRegexWSequence(wfQueue, OR_WID4("property",
					"PROPERTY", "queue", "QUEUE"), wfQueue);

	if( theQUEUE != WObject::_NULL_ )
	{
		// case of standard sequence parameters or single property parameter
		std::string strStrategy = ( theQUEUE->isWSequence() )
				? Query::getWPropertyStringOrElse(
						theQUEUE, "strategy", "queue", "BFS")
				: theQUEUE->strValue();

		mStrategy = STRATEGY_UNDEFINED;

		// popTo ALL STRATEGY
		if( strStrategy.find("ALL") != std::string::npos )
		{
			mStrategy |= STRATEGY_ALL;
		}

		// BASIC STRATEGY
		if( (strStrategy.find("BFS") != std::string::npos) ||
			REGEX_FIND(strStrategy, CONS_WID3("BREADTH", "FIRST", "SEARCH")) )
		{
			mStrategy |= STRATEGY_BFS;
		}
		else if( (strStrategy.find("DFS") != std::string::npos) ||
			REGEX_FIND(strStrategy, CONS_WID3("DEPTH", "FIRST", "SEARCH")) )
		{
			mStrategy |= STRATEGY_DFS;
		}
		else if( (strStrategy.find("RFS") != std::string::npos) ||
			REGEX_FIND(strStrategy, CONS_WID3("RAMDOM", "FIRST", "SEARCH")) )
		{
			mStrategy |= STRATEGY_RFS;
		}
		else if( strStrategy.find("XFS") != std::string::npos )
		{
			mStrategy |= STRATEGY_XFS;
		}

		else if( (strStrategy.find("BEST") != std::string::npos) ||
			REGEX_FIND(strStrategy, CONS_WID3("BEST", "FIRST", "SEARCH")) )
		{
			mStrategy |= STRATEGY_BFS;
		}

		else if( strStrategy.find("FIRST") != std::string::npos )
		{
			mStrategy |= STRATEGY_FIRST;
		}
		else if( strStrategy.find("LAST") != std::string::npos )
		{
			mStrategy |= STRATEGY_LAST;
		}

		// ORDER STRATEGY
		else if( strStrategy.find("ORDER") != std::string::npos )
		{
			mStrategy |= STRATEGY_ORDER;
		}

		// Only basic configuration in the supervisor WObject
		// Case in new concise syntax !
		if( isnotDefinedWTypedObjectParameters )
		{
			//!! NOTHING ELSE ???
		}

		// BLOCK STRATEGY
		if( strStrategy.find("BLOCK") != std::string::npos )
		{
			mStrategy |= STRATEGY_BLOCK;

			avm_size_t aBlockHeightPeriod;
			avm_size_t aBlockWidthPeriod;
			avm_size_t aBlockHeight;
			avm_size_t aBlockWidth;

			avm_size_t aHeightLimit;
			avm_size_t aWidthLimit;

			// Block height limit
			aHeightLimit = Query::getWPropertySizeT(theQUEUE, "height",
					AVM_NUMERIC_MAX_SIZE_T, AVM_NUMERIC_MAX_SIZE_T);

			// Block height period
			aBlockHeightPeriod = aBlockHeight = Query::getRegexWPropertySizeT(
					theQUEUE, CONS_WID2("block", "height"),
					AVM_NUMERIC_MAX_SIZE_T, AVM_NUMERIC_MAX_SIZE_T);


			// Block width limit
			aWidthLimit = Query::getWPropertySizeT(theQUEUE, "width",
					AVM_NUMERIC_MAX_SIZE_T, AVM_NUMERIC_MAX_SIZE_T);

			// Block width period
			aBlockWidthPeriod = aBlockWidth = Query::getRegexWPropertySizeT(
					theQUEUE, CONS_WID2("block", "width"),
					AVM_NUMERIC_MAX_SIZE_T, AVM_NUMERIC_MAX_SIZE_T);

			configureWaitingBlockStrategy(aBlockHeightPeriod, aBlockWidthPeriod,
					aBlockHeight, aBlockWidth, aHeightLimit, aWidthLimit);
		}

		// WEIGHT STRATEGY
		else if( strStrategy.find("WEIGHT") != std::string::npos )
		{
			mStrategy |= STRATEGY_WEIGHT;

			int anInteger = Query::getWPropertyInt(
					theQUEUE, "weight", DEFAULT_QUEUE_COUNT);
			if( (anInteger < 0) || (anInteger > (AVM_NUMERIC_MAX_INT8 - 1)) )
			{
				anInteger = (AVM_NUMERIC_MAX_INT8 - 1);

AVM_IF_DEBUG_FLAG( CONFIGURING )
	AVM_OS_LOG << "ExecutionQueue::configure:> Invalid weight value in [1,"
			<< (AVM_NUMERIC_MAX_INT8 - 1) << ">] ! => replace by < "
			<< anInteger << " >" << std::endl;
AVM_ENDIF_DEBUG_FLAG( CONFIGURING )
			}

			if( mStrategy & STRATEGY_ALL )
			{
				configureWaitingWeightStrategyAll((avm_uint8_t) anInteger);
			}
			else
			{
				configureWaitingWeightStrategy((avm_uint8_t) anInteger);
			}
		}

		if( mStrategy == STRATEGY_UNDEFINED )
		{
			AVM_OS_ERROR_ALERT << "ExecutionQueue::configure:> "
						"Invalid strategy ATTRIBUTE !!!"
					<< SEND_ALERT;

			mStrategy = STRATEGY_DFS;
		}

		if( mWaitingStrategy == NULL )
		{
			if( mStrategy & STRATEGY_ALL )
			{
				configureWaitingBasicStrategyAll();
			}
			else
			{
				configureWaitingBasicStrategy();
			}

			if( mWaitingStrategy == NULL )
			{
				AVM_OS_WARN << "ExecutionQueue::configure:> "
						"Failed to configure waiting strategy !";

				return( mConfigFlag = false );
			}
		}
	}
	else
	{
		AVM_OS_ERROR_ALERT << "ExecutionQueue::configure:> "
					"Expected a <queue> or PROPERTY section !!!"
				<< SEND_ALERT;

		return( mConfigFlag = false );
	}

	// Registration to handler DestroyCtx event
	getSymbexEventManager().registerHandlerEventDestroyCtx(this);

	return( mConfigFlag = true );
}


void ExecutionQueue::configureWaitingBasicStrategy()
{
	switch( mStrategy & STRATEGY_FAMILY_BASIC )
	{
		case STRATEGY_BFS:
		{
			mWaitingStrategy = new WaitingBasicStrategyBFS(1);
			break;
		}
		case STRATEGY_DFS:
		{
			mWaitingStrategy = new WaitingBasicStrategyDFS(1);
			break;
		}
		case STRATEGY_RFS:
		case STRATEGY_XFS:
		{
			mWaitingStrategy = new WaitingBasicStrategyRFS(1);
			break;
		}

		case STRATEGY_BEST:
		{
			mWaitingStrategy = new WaitingBasicStrategyBFS(1);
			break;
		}

		case STRATEGY_FIRST:
		{
			mWaitingStrategy = new WaitingBasicStrategyFIRST(1);
			break;
		}
		case STRATEGY_LAST:
		{
			mWaitingStrategy = new WaitingBasicStrategyLAST(1);
			break;
		}

		case STRATEGY_ORDER:
		{
			mWaitingStrategy = new WaitingBasicStrategyORDER(1);
			break;
		}

		default:
		{
			mWaitingStrategy = new WaitingBasicStrategyBFS(1);
			break;
		}
	}
}


void ExecutionQueue::configureWaitingBasicStrategyAll()
{
	switch( mStrategy & STRATEGY_FAMILY_BASIC_ALL )
	{
		case STRATEGY_BFS:
		{
			mWaitingStrategy = new WaitingBasicStrategyALL<
					WaitingBasicStrategyBFS >(1);
			break;
		}
		case STRATEGY_DFS:
		{
			mWaitingStrategy = new WaitingBasicStrategyALL<
					WaitingBasicStrategyDFS >(1);
			break;
		}
		case STRATEGY_RFS:
		case STRATEGY_XFS:
		{
			mWaitingStrategy = new WaitingBasicStrategyALL<
					WaitingBasicStrategyRFS >(1);
			break;
		}

		case STRATEGY_BEST:
		{
			mWaitingStrategy = new WaitingBasicStrategyALL<
					WaitingBasicStrategyBFS >(1);
			break;
		}

		case STRATEGY_FIRST:
		{
			mWaitingStrategy = new WaitingBasicStrategyALL<
					WaitingBasicStrategyFIRST >(1);
			break;
		}
		case STRATEGY_LAST:
		{
			mWaitingStrategy = new WaitingBasicStrategyALL<
					WaitingBasicStrategyLAST >(1);
			break;
		}

		case STRATEGY_ORDER:
		{
			mWaitingStrategy = new WaitingBasicStrategyALL<
					WaitingBasicStrategyORDER >(1);
			break;
		}

		case STRATEGY_ALL:
		default:
		{
			mWaitingStrategy = new WaitingBasicStrategyALL<
					WaitingBasicStrategyBFS >(1);
			break;
		}
	}
}



void ExecutionQueue::configureWaitingBlockStrategy(
		avm_size_t aBlockHeightPeriod, avm_size_t aBlockWidthPeriod,
		avm_size_t aBlockHeight, avm_size_t aBlockWidth,
		avm_size_t aHeightLimit, avm_size_t aWidthLimit)
{
	switch( mStrategy & STRATEGY_FAMILY_BASIC_ALL )
	{
		case STRATEGY_BFS:
		{
			mWaitingStrategy = new WaitingStrategyBLOCK_BFS(
					getConfiguration(), 1, aBlockHeightPeriod,
					aBlockWidthPeriod, aBlockHeight,
					aBlockWidth, aHeightLimit, aWidthLimit);
			break;
		}
		case STRATEGY_DFS:
		{
			mWaitingStrategy = new WaitingStrategyBLOCK_DFS(
					getConfiguration(), 1, aBlockHeightPeriod,
					aBlockWidthPeriod, aBlockHeight,
					aBlockWidth, aHeightLimit, aWidthLimit);
			break;
		}
		case STRATEGY_RFS:
		case STRATEGY_XFS:
		{
			mWaitingStrategy = new WaitingStrategyBLOCK_RFS(
					getConfiguration(), 1, aBlockHeightPeriod,
					aBlockWidthPeriod, aBlockHeight,
					aBlockWidth, aHeightLimit, aWidthLimit);
			break;
		}

		case STRATEGY_BEST:
		{
			mWaitingStrategy = new WaitingStrategyBLOCK_BFS(
					getConfiguration(), 1, aBlockHeightPeriod,
					aBlockWidthPeriod, aBlockHeight,
					aBlockWidth, aHeightLimit, aWidthLimit);
			break;
		}

//		case STRATEGY_FIRST:
//		case STRATEGY_LAST:
//
//		case STRATEGY_ORDER:

		case STRATEGY_ALL:
		{
			mWaitingStrategy = new WaitingStrategyBLOCK_ALL<
					WaitingBasicStrategyALL< WaitingBasicStrategyBFS > >(
							getConfiguration(), 1, aBlockHeightPeriod,
							aBlockWidthPeriod, aBlockHeight,
							aBlockWidth, aHeightLimit, aWidthLimit);
			break;
		}
		default:
		{
			mWaitingStrategy = new WaitingStrategyBLOCK_BFS(
					getConfiguration(),  1, aBlockHeightPeriod,
					aBlockWidthPeriod, aBlockHeight,
					aBlockWidth, aHeightLimit, aWidthLimit);
			break;
		}
	}
}


void ExecutionQueue::configureWaitingWeightStrategy(avm_uint8_t maxWeight)
{
	switch( mStrategy & STRATEGY_FAMILY_BASIC )
	{
		case STRATEGY_BFS:
		{
			mWaitingStrategy = new WaitingStrategyWEIGHT<
					WaitingBasicStrategyBFS >(maxWeight);
			break;
		}
		case STRATEGY_DFS:
		{
			mWaitingStrategy = new WaitingStrategyWEIGHT<
					WaitingBasicStrategyDFS >(maxWeight);
			break;
		}
		case STRATEGY_RFS:
		case STRATEGY_XFS:
		{
			mWaitingStrategy = new WaitingStrategyWEIGHT<
					WaitingBasicStrategyRFS >(maxWeight);
			break;
		}

		case STRATEGY_BEST:
		{
			mWaitingStrategy = new WaitingStrategyWEIGHT<
					WaitingBasicStrategyBFS >(maxWeight);
			break;
		}

		case STRATEGY_FIRST:
		{
			mWaitingStrategy = new WaitingStrategyWEIGHT<
					WaitingBasicStrategyFIRST >(maxWeight);
			break;
		}
		case STRATEGY_LAST:
		{
			mWaitingStrategy = new WaitingStrategyWEIGHT<
					WaitingBasicStrategyLAST >(maxWeight);
			break;
		}

//		case STRATEGY_ORDER:

		default:
		{
			mWaitingStrategy = new WaitingStrategyWEIGHT<
					WaitingBasicStrategyBFS >(maxWeight);
			break;
		}
	}
}


void ExecutionQueue::configureWaitingWeightStrategyAll(avm_uint8_t maxWeight)
{
	switch( mStrategy & STRATEGY_FAMILY_BASIC_ALL )
	{
		case STRATEGY_BFS:
		{
			mWaitingStrategy = new WaitingStrategyWEIGHT<
				WaitingBasicStrategyALL<
						WaitingBasicStrategyBFS > >(maxWeight);
			break;
		}
		case STRATEGY_DFS:
		{
			mWaitingStrategy = new WaitingStrategyWEIGHT<
				WaitingBasicStrategyALL<
						WaitingBasicStrategyDFS > >(maxWeight);
			break;
		}
		case STRATEGY_RFS:
		case STRATEGY_XFS:
		{
			mWaitingStrategy = new WaitingStrategyWEIGHT<
				WaitingBasicStrategyALL<
						WaitingBasicStrategyRFS > >(maxWeight);
			break;
		}

		case STRATEGY_BEST:
		{
			mWaitingStrategy = new WaitingStrategyWEIGHT<
				WaitingBasicStrategyALL<
						WaitingBasicStrategyBFS > >(maxWeight);
			break;
		}

		case STRATEGY_FIRST:
		{
			mWaitingStrategy = new WaitingStrategyWEIGHT<
				WaitingBasicStrategyALL<
						WaitingBasicStrategyFIRST > >(maxWeight);
			break;
		}
		case STRATEGY_LAST:
		{
			mWaitingStrategy = new WaitingStrategyWEIGHT<
				WaitingBasicStrategyALL<
						WaitingBasicStrategyLAST > >(maxWeight);
			break;
		}

//		case STRATEGY_ORDER:

		case STRATEGY_ALL:
		default:
		{
			mWaitingStrategy = new WaitingStrategyWEIGHT<
				WaitingBasicStrategyALL<
						WaitingBasicStrategyBFS > >(maxWeight);
			break;
		}
	}
}


/**
 * RECONFIGURATION
 */
bool ExecutionQueue::reconfigure(
		ENUM_STRATEGY_T newStrategy, avm_uint8_t queueCount)
{
	if( (mStrategy == newStrategy) && (mWaitingStrategy != NULL) )
	{
		return( true );
	}

	if( newStrategy == STRATEGY_UNDEFINED)
	{
		return( false );
	}
	// Unsupported BLOCK strategy, see reconfigureBlock(...)
	else if( (newStrategy & STRATEGY_BLOCK) != 0 )
	{
		return( false );
	}

	// destroy current waiting strategy
	if( mWaitingStrategy != NULL )
	{
		delete mWaitingStrategy;

		mWaitingStrategy = NULL;
	}
	mStrategy = newStrategy;

	/**
	 * Reconfigure supported strategy
	 */
	// WEIGHT strategy
	if( (mStrategy & STRATEGY_WEIGHT) != 0 )
	{
		if( mStrategy & STRATEGY_ALL )
		{
			configureWaitingWeightStrategyAll(queueCount);
		}
		else
		{
			configureWaitingWeightStrategy(queueCount);
		}
	}

	// ALL family strategy
	else if( (mStrategy & STRATEGY_ALL) != 0 )
	{
		configureWaitingBasicStrategyAll();
	}
	// basic strategy
	else
	{
		configureWaitingBasicStrategy();
	}


	if( mWaitingStrategy == NULL )
	{
		AVM_OS_WARN << "ExecutionQueue::reconfigure:> "
				"Failed to reconfigure waiting strategy !";

		return( false );
	}

	return( mWaitingStrategy != NULL );
}


bool ExecutionQueue::reconfigureBlock(ENUM_STRATEGY_T newStrategy,
		avm_size_t aBlockHeightPeriod, avm_size_t aBlockWidthPeriod,
		avm_size_t aBlockHeight, avm_size_t aBlockWidth,
		avm_size_t aHeightLimit, avm_size_t aWidthLimit)
{
	if( (mStrategy == newStrategy) && (mWaitingStrategy != NULL) )
	{
		return( true );
	}
	else if( (newStrategy & STRATEGY_BLOCK) == 0  )
	{
		AVM_OS_WARN << "ExecutionQueue::reconfigureBlock:> "
				"Unexpected a non-block as waiting strategy !";

		return( false );
	}

	// destroy current waiting strategy
	if( mWaitingStrategy != NULL )
	{
		delete mWaitingStrategy;

		mWaitingStrategy = NULL;
	}
	mStrategy = newStrategy;

	/**
	 * Reconfigure block strategy
	 */
	configureWaitingBlockStrategy(aBlockHeightPeriod, aBlockWidthPeriod,
			aBlockHeight, aBlockWidth, aHeightLimit, aWidthLimit);

	if( mWaitingStrategy == NULL )
	{
		AVM_OS_WARN << "ExecutionQueue::reconfigureBlock:> "
				"Failed to reconfigureBlock waiting strategy !";

		return( false );
	}

	return( mWaitingStrategy != NULL );
}


/**
 * GETTER - SETTER
 * mWaitingStrategyStack
 * mWaitingStrategy
 */
bool ExecutionQueue::pushWaitingStrategy(
		WaitingStrategy * aWaitingStrategy, bool spliceContainedFlag)
{
	if( aWaitingStrategy == NULL )
	{
		return( false );
	}

	if( spliceContainedFlag )
	{
		aWaitingStrategy->splice( *mWaitingStrategy );
	}

	mWaitingStrategyStack.push( mWaitingStrategy );

	mWaitingStrategy = aWaitingStrategy;

	return( true );
}

bool ExecutionQueue::popWaitingStrategy(
		bool spliceContainedFlag, bool destroyCurrentFlag)
{
	if( mWaitingStrategyStack.empty() )
	{
		return( false );
	}

	if( mWaitingStrategy != NULL )
	{
		if( spliceContainedFlag )
		{
			mWaitingStrategyStack.top()->splice( *mWaitingStrategy );
		}
		if( destroyCurrentFlag )
		{
			delete mWaitingStrategy;
		}
	}

	mWaitingStrategy = mWaitingStrategyStack.top();

	mWaitingStrategyStack.pop();

	return( true );
}


/**
 * REPORT TRACE
 */
void ExecutionQueue::reportDefault(OutStream & os) const
{
//AVM_IF_DEBUG_FLAG( PROCESSOR )
	os << TAB << "EXECUTION QUEUE" << std::endl;

	os << TAB2 << "strategy : " << strStrategy() << EOL_FLUSH;

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , REPORTING , COMPUTING )

	os << incr_stream( *this );

AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , REPORTING , COMPUTING )
//AVM_ENDIF_DEBUG_FLAG( PROCESSOR )
}


/**
 * TRACE Queue
 */
void ExecutionQueue::traceQueue(OutStream & os,
		ListOfExecutionContext & aQueue, const std::string & aMessage)
{
	os << TAB << aMessage << " << size : " << aQueue.size() << " >> "
			<< EOL_INCR_INDENT;

	ListOfExecutionContext::iterator it = aQueue.begin();
	ListOfExecutionContext::iterator itEnd = aQueue.end();
	for( ; it != itEnd ; ++it )
	{
		(*it)->traceDefault(os);
	}
	os << DECR_INDENT;
}


/**
 * Serialization
 */
std::string ExecutionQueue::strStrategy() const
{
	if( mStrategy == STRATEGY_UNDEFINED )
	{
		return( "UNDEFINED" );
	}
	else
	{
		std::ostringstream oss;

		if( (mStrategy & STRATEGY_BLOCK) != 0 )
		{
			oss << "#BLOCK";
		}
		if( (mStrategy & STRATEGY_WEIGHT) != 0 )
		{
			oss << "#WEIGHT";
		}

		if( (mStrategy & STRATEGY_ALL) != 0 )
		{
			oss << "#ALL";
		}

		if( (mStrategy & STRATEGY_DFS) != 0 )
		{
			oss << "#DFS";
		}
		if( (mStrategy & STRATEGY_BFS) != 0 )
		{
			oss << "#BFS";
		}
		if( (mStrategy & STRATEGY_RFS) != 0 )
		{
			oss << "#RFS";
		}
		if( (mStrategy & STRATEGY_XFS) != 0 )
		{
			oss << "#XFS";
		}

		if( (mStrategy & STRATEGY_BEST) != 0 )
		{
			oss << "#BEST";
		}

		if( (mStrategy & STRATEGY_FIRST) != 0 )
		{
			oss << "#FIRST";
		}
		if( (mStrategy & STRATEGY_LAST) != 0 )
		{
			oss << "#LAST";
		}

		if( (mStrategy & STRATEGY_ORDER) != 0 )
		{
			oss << "#ORDER";
		}

		return( oss.str() );
	}
}


void ExecutionQueue::toStream(OutStream & os) const
{
	os << TAB << "queue " << strUniqId() << " {" << EOL;

	if( mInitQueue.nonempty() )
	{
		os << TAB << "init< size: " << mInitQueue.size() << " >:"
				<< EOL_INCR_INDENT;

		toStream(mInitQueue, os);
		os << DECR_INDENT;
	}

	if( hasWaiting() )
	{
		mWaitingStrategy->toStream(os);
	}

	if( mFailedQueue.nonempty() )
	{
		os << TAB << "failed< size: " << mFailedQueue.size() << " >:"
				<< EOL_INCR_INDENT;

		toStream(mFailedQueue, os);
		os << DECR_INDENT;
	}

	if( mReadyQueue.nonempty() )
	{
		os << TAB << "ready< size: " << mReadyQueue.size() << " >:"
				<< EOL_INCR_INDENT;

		toStream(mReadyQueue, os);
		os << DECR_INDENT;
	}

	if( mResultQueue.nonempty() )
	{
		os << TAB << "result< size: " << mResultQueue.size() << " >:"
				<< EOL_INCR_INDENT;

		toStream(mResultQueue, os);
		os << DECR_INDENT;
	}

	os << TAB << "}" << EOL;
}

void ExecutionQueue::toStream(
		const ListOfExecutionContext & aQueue, OutStream & os) const
{
	ListOfExecutionContext::const_iterator itEC = aQueue.begin();
	ListOfExecutionContext::const_iterator itEnd = aQueue.end();
	for( ; itEC != itEnd ; ++itEC )
	{
		if( ((*itEC) != NULL) && (*itEC)->isAlive() )
		{
			(*itEC)->traceDefault(os);
		}

	}
}



}
