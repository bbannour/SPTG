/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 18 févr. 2013
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef WAITINGBASICSTRATEGY_H_
#define WAITINGBASICSTRATEGY_H_

#include "WaitingStrategy.h"


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// ALL WAITING STRATEGY
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

template< class BasicStrategy >
class WaitingBasicStrategyALL  :  public BasicStrategy
{

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	WaitingBasicStrategyALL(avm_uint8_t queueCount = 1)
	: BasicStrategy( queueCount )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~WaitingBasicStrategyALL()
	{
		//!! NOTHING
	}


	////////////////////////////////////////////////////////////////////////////
	// POP WAITING BEHAVIOR API
	////////////////////////////////////////////////////////////////////////////

	inline virtual void popTo(ListOfExecutionContext & aReadyQueue)
	{
		aReadyQueue.splice(BasicStrategy::mQueueCache.nonempty() ?
				BasicStrategy::mQueueCache : BasicStrategy::mQueue);
	}


	inline virtual void popTo(avm_uint8_t aQueueTableOffset,
			ListOfExecutionContext & aReadyQueue)
	{
		aReadyQueue.splice( BasicStrategy::mQueueTable
				[ (aQueueTableOffset < BasicStrategy::mQueueCount) ?
				aQueueTableOffset : BasicStrategy::mQueueCount ] );
	}


};


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// BFS < BREADTH_FIRST_SEARCH >  WAITING STRATEGY
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class WaitingBasicStrategyBFS :
		public WaitingStrategyImpl<
				StrategyPushBack , ChildIteratorFIFO , StrategyPopFront >
{

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	WaitingBasicStrategyBFS(avm_uint8_t queueCount = 1)
	: WaitingStrategyImpl( queueCount )
	{
		//!! NOTHING
	}
};


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// DFS < DEPTH_FIRST_SEARCH >  WAITING STRATEGY
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class WaitingBasicStrategyDFS :
		public WaitingStrategyImpl<
				StrategyPushBack , ChildIteratorLIFO , StrategyPopBack >
{

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	WaitingBasicStrategyDFS(avm_uint8_t queueCount = 1)
	: WaitingStrategyImpl( queueCount )
	{
		//!! NOTHING
	}
};


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// RFS < RANDOM_FIRST_SEARCH > WAITING STRATEGY
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class WaitingBasicStrategyRFS :
		public WaitingStrategyImpl<
				StrategyPushBack , ChildIteratorFIFO , StrategyPopRandom >
{

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	WaitingBasicStrategyRFS(avm_uint8_t queueCount = 1)
	: WaitingStrategyImpl( queueCount )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~WaitingBasicStrategyRFS()
	{
		//!! NOTHING
	}


	// UNDEF TOP FOR RANDOM ACCESS
	inline virtual ExecutionContext * top()
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "Illegal invocation of "
					"<< WaitingBasicStrategyALL::top() >> !!!"
				<< SEND_EXIT;

		return( NULL );
	}

	inline virtual ExecutionContext * top(avm_uint8_t aQueueTableOffset)
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "Illegal invocation of "
					"<< WaitingBasicStrategyRFS::top(queueOffset) >> !!!"
				<< SEND_EXIT;

		return( NULL );
	}

	inline virtual ExecutionContext * topFrom(ListOfExecutionContext & aQueue)
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "Illegal invocation of "
					"<< WaitingBasicStrategyRFS::topFrom(queue) >> !!!"
				<< SEND_EXIT;

		return( NULL );
	}

};


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// FIRST  WAITING STRATEGY
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class WaitingBasicStrategyFIRST :
		public WaitingStrategyImpl<
				StrategyPushFront , ChildIteratorLIFO , StrategyPopFront >
{

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	WaitingBasicStrategyFIRST(avm_uint8_t queueCount = 1)
	: WaitingStrategyImpl( queueCount )
	{
		//!! NOTHING
	}
};



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// LAST WAITING STRATEGY
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class WaitingBasicStrategyLAST :
		public WaitingStrategyImpl<
				StrategyPushBack , ChildIteratorLIFO , StrategyPopBack >
{

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	WaitingBasicStrategyLAST(avm_uint8_t queueCount = 1)
	: WaitingStrategyImpl( queueCount )
	{
		//!! NOTHING
	}
};





////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// ORDER  WAITING STRATEGY
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class WaitingBasicStrategyORDER :
		public WaitingStrategyImpl<
				StrategyPushOrder , ChildIteratorFIFO , StrategyPopFront >
{

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	WaitingBasicStrategyORDER(avm_uint8_t queueCount = 1)
	: WaitingStrategyImpl( queueCount )
	{
		//!! NOTHING
	}
};




} /* namespace sep */
#endif /* WAITINGBASICSTRATEGY_H_ */
