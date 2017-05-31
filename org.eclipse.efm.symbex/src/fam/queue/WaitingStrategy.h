/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 10 févr. 2013
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef FAM_QUEUE_WAITINGSTRATEGY_H_
#define FAM_QUEUE_WAITINGSTRATEGY_H_


#include <collection/Typedef.h>

#include <fml/runtime/ExecutionContext.h>

#include <fam/api/AbstractProcessorUnit.h>


namespace sep
{


class AbstractProcessorUnit;

class ExecutionContext;

class TargetFilter;


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// ABSTRACT WAITING STRATEGY
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class WaitingStrategy
{

protected:
	/**
	 * ATTRIBUTES
	 */
	// les contextes qui attendent sagement qu'on s'intéresse à eux pour passer
	// l'audition conduisant à l'exécution !!!!!
	avm_uint8_t mQueueCount;
	ListOfExecutionContext * mQueueTable;
	avm_uint8_t tOffset;

	static const avm_uint8_t QUEUE_CACHE = 0;
	static const avm_uint8_t QUEUE_OTHER = 1;

	ListOfExecutionContext & mQueueCache;
	ListOfExecutionContext & mQueue;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	WaitingStrategy(avm_uint8_t queueCount = 1)
	: //mWaitingBasicStrategy( NULL ),
	mQueueCount( queueCount ),
	mQueueTable( new ListOfExecutionContext[mQueueCount + 1] ),
	tOffset( 0 ),

	mQueueCache( mQueueTable[QUEUE_CACHE] ),
	mQueue( mQueueTable[QUEUE_OTHER] )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~WaitingStrategy()
	{
		delete( mQueueTable );
	}

	/**
	 * GETTER - SETTER
	 * Target Filter
	 */
	inline virtual TargetFilter * getTargetFilter()
	{
		return( NULL );
	}

	inline virtual bool hasTargetFilter() const
	{
		return( false );
	}

	inline virtual void setTargetFilter(TargetFilter * aTargetFilter)
	{
		//!! NOTHING
	}


	/**
	 * GETTER - SETTER
	 * mQueueTable
	 */
	inline void clearQueueTable()
	{
		for( tOffset = 0 ; tOffset <= mQueueCount ; ++tOffset )
		{
			if( mQueueTable[ tOffset ].nonempty() )
			{
				mQueueTable[ tOffset ].clear();
			}
		}
	}


	inline ListOfExecutionContext * getQueueTable()
	{
		return( mQueueTable );
	}

	inline void getQueueTable(ListOfExecutionContext & listOfEC)
	{
		for( tOffset = 0 ; tOffset <= mQueueCount ; ++tOffset )
		{
			if( mQueueTable[ tOffset ].nonempty() )
			{
				listOfEC.append( mQueueTable[ tOffset ] );
			}
		}
	}


	inline void spliceQueueTable(ListOfExecutionContext & listOfEC)
	{
		for( tOffset = 0 ; tOffset <= mQueueCount ; ++tOffset )
		{
			if( mQueueTable[ tOffset ].nonempty() )
			{
				listOfEC.splice( mQueueTable[ tOffset ] );
			}
		}
	}

	inline void spliceQueueTable(
			ListOfExecutionContext & listOfEC, avm_uint8_t tOffsetMax)
	{
		if( tOffsetMax > mQueueCount )
		{
			tOffsetMax = mQueueCount;
		}
		for( tOffset = 0 ; tOffset <= tOffsetMax ; ++tOffset )
		{
			if( mQueueTable[ tOffset ].nonempty() )
			{
				listOfEC.splice( mQueueTable[ tOffset ] );
			}
		}
	}


	inline avm_uint8_t splicePriorQueueTable(ListOfExecutionContext & listOfEC)
	{
		for( tOffset = 0 ; tOffset <= mQueueCount ; ++tOffset )
		{
			if( mQueueTable[ tOffset ].nonempty() )
			{
				listOfEC.splice( mQueueTable[ tOffset ] );
				break;
			}
		}

		return( tOffset );
	}

	inline avm_uint8_t splicePriorQueueTable(ListOfExecutionContext & listOfEC,
			avm_uint8_t anOffsetMin, avm_uint8_t tOffsetMax)
	{
		for( tOffset = anOffsetMin ; tOffset <= tOffsetMax ; ++tOffset )
		{

			if( mQueueTable[ tOffset ].nonempty() )
			{
				listOfEC.splice( mQueueTable[ tOffset ] );
				break;
			}
		}

		return( tOffset );
	}


	inline void clearQueue()
	{
		mQueue.clear();
	}

	inline ListOfExecutionContext & getQueue()
	{
		return( mQueue );
	}


	inline void clearCache()
	{
		mQueueCache.clear();
	}

	inline ListOfExecutionContext & getCache()
	{
		return( mQueueCache );
	}


	inline bool hasWaiting()
	{
		for( tOffset = 0 ; tOffset <= mQueueCount ; ++tOffset )
		{
			if( mQueueTable[ tOffset ].nonempty() )
			{
				return( true );
			}
		}

		return( false );
	}

	inline bool hasWaiting(avm_uint8_t tOffsetMax)
	{
		for( tOffset = 0 ; tOffset <= tOffsetMax ; ++tOffset )
		{
			if( mQueueTable[ tOffset ].nonempty() )
			{
				return( true );
			}
		}

		return( false );
	}


	inline avm_size_t sizeWaiting() const
	{
		avm_size_t wsize = 0;
		for( avm_size_t tOffset = 0 ; tOffset <= mQueueCount ; ++tOffset )
		{
			if( mQueueTable[ tOffset ].nonempty() )
			{
				wsize += mQueueTable[ tOffset ].size();
			}
		}

		return( wsize );
	}

	inline void remove(ExecutionContext * anEC)
	{
		for( tOffset = 0 ; tOffset <= mQueueCount ; ++tOffset )
		{
			if( mQueueTable[ tOffset ].nonempty() )
			{
				mQueueTable[ tOffset ].remove(anEC);
			}
		}
	}


	inline void traceQueue(const ListOfExecutionContext & aQueue,
			OutStream & os, const std::string & aMessage)
	{
		os << TAB << aMessage << " << size : " << aQueue.size() << " >> "
				<< EOL_INCR_INDENT;

		ListOfExecutionContext::const_iterator it = aQueue.begin();
		ListOfExecutionContext::const_iterator itEnd = aQueue.end();
		for( ; it != itEnd ; ++it )
		{
			(*it)->traceDefault(os);
		}
		os << DECR_INDENT;
	}

	inline void trace(OutStream & os, const std::string & aMessage)
	{
		for( avm_size_t tOffset = 0 ; tOffset <= mQueueCount ; ++tOffset )
		{
			if( mQueueTable[ tOffset ].nonempty() )
			{
				traceQueue(mQueueTable[ tOffset ], os,
						OSS() << aMessage << '[' << tOffset << ']');
			}
		}
	}

	inline void toStream(OutStream & os) const
	{
		os << TAB << "waiting< size: " << sizeWaiting() << " >:"
				<< EOL_INCR_INDENT;

		for( avm_size_t tOffset = 0 ; tOffset <= mQueueCount ; ++tOffset )
		{
			if( mQueueTable[ tOffset ].nonempty() )
			{
				os << TAB2 << "table< weight:" << tOffset
						<< " , size:" << mQueueTable[ tOffset ].size()
						<< " >:" << EOL_INCR_INDENT;
				toStream(mQueueTable[ tOffset ], os);
				os << DECR_INDENT;
			}
		}
		os << DECR_INDENT;
	}

	inline void toStream(
			const ListOfExecutionContext & aQueue, OutStream & os) const
	{
		ListOfExecutionContext::const_iterator itEC = aQueue.begin();
		ListOfExecutionContext::const_iterator itEnd = aQueue.end();
		for( ; itEC != itEnd ; ++itEC )
		{
			(*itEC)->traceDefault(os);

		}
	}



	////////////////////////////////////////////////////////////////////////////
	// PUSH WAITING BEHAVIOR API
	////////////////////////////////////////////////////////////////////////////

	/**
	 * PUSH
	 */
	virtual void push(ExecutionContext * anEC) = 0;

	inline virtual void push(const ListOfExecutionContext & listofEC)
	{
		ListOfExecutionContext::const_iterator itEC = listofEC.begin();
		ListOfExecutionContext::const_iterator endEC = listofEC.end();
		for( ; itEC != endEC ; ++itEC )
		{
			push( *itEC );
		}
	}

	virtual void push(avm_uint8_t aQueueTableOffset,
			ExecutionContext * anEC) = 0;

	virtual void push(ListOfExecutionContext & aQueue,
			ExecutionContext * anEC) = 0;


	inline virtual void pushCache(ExecutionContext * anEC)
	{
		push(mQueueCache, anEC);
	}

	/**
	 * SPLICE
	 */
	inline virtual void splice(WaitingStrategy & aWaitingStrategy)
	{
		for( tOffset = 0 ; tOffset <= aWaitingStrategy.mQueueCount ; ++tOffset )
		{
			push( aWaitingStrategy.mQueueTable[ tOffset ] );
		}

		aWaitingStrategy.clearQueueTable();
	}

	inline virtual void splice(avm_uint8_t aQueueTableOffset,
			ListOfExecutionContext & listofEC)
	{
		mQueueTable[ (aQueueTableOffset < mQueueCount) ?
				aQueueTableOffset : mQueueCount ].splice( listofEC );
	}



	////////////////////////////////////////////////////////////////////////////
	// PUSH#CHILD WAITING BEHAVIOR API
	////////////////////////////////////////////////////////////////////////////

	virtual void pushChild(const ListOfExecutionContext & childEC) = 0;

	virtual void pushChild(avm_uint8_t aQueueTableOffset,
			ListOfExecutionContext & childEC) = 0;

	virtual void pushChild(ListOfExecutionContext & aQueue,
			ListOfExecutionContext & childEC) = 0;


	////////////////////////////////////////////////////////////////////////////
	// POP WAITING BEHAVIOR API
	////////////////////////////////////////////////////////////////////////////

	virtual ExecutionContext * pop() = 0;

	virtual void popTo(ListOfExecutionContext & aReadyQueue) = 0;

	virtual ExecutionContext * pop(avm_uint8_t aQueueTableOffset) = 0;

	virtual void popTo(avm_uint8_t aQueueTableOffset,
			ListOfExecutionContext & aReadyQueue) = 0;

	virtual ExecutionContext * popFrom(ListOfExecutionContext & aQueue) = 0;


	////////////////////////////////////////////////////////////////////////////
	// TOP WAITING BEHAVIOR API
	////////////////////////////////////////////////////////////////////////////

	virtual ExecutionContext * top() = 0;

	virtual ExecutionContext * top(avm_uint8_t aQueueTableOffset) = 0;

	virtual ExecutionContext * topFrom(ListOfExecutionContext & aQueue) = 0;


	////////////////////////////////////////////////////////////////////////////
	// REQUEUE REQUEST  WAITING BEHAVIOR API
	////////////////////////////////////////////////////////////////////////////

	inline virtual void handleRequestRequeueWaiting(
			AbstractProcessorUnit * aRequestor)
	{
		aRequestor->handleRequestRequeueWaitingTable((*this), 0, mQueueCount);
	}

	inline virtual void handleRequestRequeueReserve(
			AbstractProcessorUnit * aRequestor,
			ListOfExecutionContext & aReserveQueue)
	{
		aRequestor->handleRequestRequeueReserveTable(
				(*this), aReserveQueue, 0, mQueueCount );
	}

};



////////////////////////////////////////////////////////////////////////////////
// BASIC STRATEGY PUSH
////////////////////////////////////////////////////////////////////////////////

struct StrategyPushBack
{
	inline static void push(ListOfExecutionContext & aQueue,
			ExecutionContext * anEC)
	{
		aQueue.push_back( anEC );
	}
};

struct StrategyPushFront
{
	inline static void push(ListOfExecutionContext & aQueue,
			ExecutionContext * anEC)
	{
		aQueue.push_front( anEC );
	}
};

struct StrategyPushOrder
{
	inline static void push(ListOfExecutionContext & aQueue,
			ExecutionContext * anEC)
	{
		avm_uint8_t weight = anEC->getWeight();

		ListOfExecutionContext::iterator itEC = aQueue.begin();
		ListOfExecutionContext::iterator itEnd = aQueue.end();
		for( ; itEC != itEnd ; ++itEC )
		{
			if( (*itEC)->getWeight() >= weight )
			{
				break;
			}
		}
		aQueue.insert( itEC , anEC);
	}
};


////////////////////////////////////////////////////////////////////////////////
// BASIC STRATEGY PUSH for CHILD
////////////////////////////////////////////////////////////////////////////////

struct ChildIteratorFIFO
{
	typedef ListOfExecutionContext::const_iterator const_child_iterator;

	inline static const_child_iterator begin_child(
			const ListOfExecutionContext & childEC)
	{
		return( childEC.begin() );
	}

	inline static const_child_iterator end_child(
			const ListOfExecutionContext & childEC)
	{
		return( childEC.end() );
	}
};


struct ChildIteratorLIFO
{
	typedef ListOfExecutionContext::const_reverse_iterator const_child_iterator;

	inline static const_child_iterator begin_child(
			const ListOfExecutionContext & childEC)
	{
		return( childEC.rbegin() );
	}

	inline static const_child_iterator end_child(
			const ListOfExecutionContext & childEC)
	{
		return( childEC.rend() );
	}
};


////////////////////////////////////////////////////////////////////////////////
// BASIC STRATEGY POP
////////////////////////////////////////////////////////////////////////////////

struct StrategyPopBack
{
	inline static ExecutionContext * popFrom(ListOfExecutionContext & aQueue)
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( aQueue.nonempty() )
				<< "Unexpected an empty execution Queue !!!"
				<< SEND_EXIT;

		return( aQueue.pop_last() );
	}

	inline static ExecutionContext * topFrom(ListOfExecutionContext & aQueue)
	{
		if( aQueue.nonempty() )
		{
			return( aQueue.last() );
		}

		return( NULL );
	}

};

struct StrategyPopFront
{
	inline static ExecutionContext * popFrom(ListOfExecutionContext & aQueue)
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( aQueue.nonempty() )
				<< "Unexpected an empty execution Queue !!!"
				<< SEND_EXIT;

		return( aQueue.pop_first() );
	}

	inline static ExecutionContext * topFrom(ListOfExecutionContext & aQueue)
	{
		if( aQueue.nonempty() )
		{
			return( aQueue.first() );
		}
		return( NULL );
	}

};


struct StrategyPopRandom
{
	inline static ExecutionContext * popFrom(ListOfExecutionContext & aQueue)
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( aQueue.nonempty() )
				<< "Unexpected an empty execution Queue !!!"
				<< SEND_EXIT;

		return( aQueue.pop_index(RANDOM::gen_uint(0, aQueue.size() - 1)) );
	}

	inline static ExecutionContext * topFrom(ListOfExecutionContext & aQueue)
	{
		return( NULL );
	}

};



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// ABSTRACT WAITING STRATEGY
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

template< class StrategyPush , class ChildIterator , class StrategyPop >
class WaitingStrategyImpl :
		public WaitingStrategy,
		public ChildIterator
{

public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	WaitingStrategyImpl(avm_uint8_t queueCount = 1)
	: WaitingStrategy( queueCount )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~WaitingStrategyImpl()
	{
		//!! NOTHING
	}


	////////////////////////////////////////////////////////////////////////////
	// PUSH WAITING BEHAVIOR API
	////////////////////////////////////////////////////////////////////////////

	/**
	 * PUSH
	 */
	inline virtual void push(ExecutionContext * anEC)
	{
		push( mQueue , anEC );
	}

	inline virtual void push(avm_uint8_t aQueueTableOffset,
			ExecutionContext * anEC)
	{
		push( mQueueTable[ (aQueueTableOffset < mQueueCount) ?
				aQueueTableOffset : mQueueCount ] , anEC );
	}

	inline virtual void push(ListOfExecutionContext & aQueue,
			ExecutionContext * anEC)
	{
		StrategyPush::push( aQueue , anEC );
	}


	////////////////////////////////////////////////////////////////////////////
	// PUSH#CHILD WAITING BEHAVIOR API
	////////////////////////////////////////////////////////////////////////////

	typename ChildIterator::const_child_iterator itEC;
	typename ChildIterator::const_child_iterator itEnd;


	inline virtual void pushChild(const ListOfExecutionContext & childEC)
	{
		itEC = ChildIterator::begin_child( childEC );
		itEnd = ChildIterator::end_child( childEC );
		for( ; itEC != itEnd ; ++itEC )
		{
			push( *itEC );
		}
	}

	inline virtual void pushChild(avm_uint8_t aQueueTableOffset,
			ListOfExecutionContext & childEC)
	{
		itEC = ChildIterator::begin_child( childEC );
		itEnd = ChildIterator::end_child( childEC );
		for( ; itEC != itEnd ; ++itEC )
		{
			push( aQueueTableOffset , *itEC );
		}
	}

	inline virtual void pushChild(ListOfExecutionContext & aQueue,
			ListOfExecutionContext & childEC)
	{
		itEC = ChildIterator::begin_child( childEC );
		itEnd = ChildIterator::end_child( childEC );
		for( ; itEC != itEnd ; ++itEC )
		{
			push( aQueue , *itEC );
		}
	}


	////////////////////////////////////////////////////////////////////////////
	// POP WAITING BEHAVIOR API
	////////////////////////////////////////////////////////////////////////////

	inline virtual ExecutionContext * pop()
	{
		return( popFrom(mQueueCache.nonempty() ? mQueueCache : mQueue) );
	}

	virtual void popTo(ListOfExecutionContext & aReadyQueue)
	{
		aReadyQueue.append( pop() );
	}

	inline virtual ExecutionContext * pop(avm_uint8_t aQueueTableOffset)
	{
		return( popFrom( mQueueTable[ (aQueueTableOffset < mQueueCount) ?
				aQueueTableOffset : mQueueCount ] ) );
	}

	virtual void popTo(avm_uint8_t aQueueTableOffset,
			ListOfExecutionContext & aReadyQueue)
	{
		aReadyQueue.append( pop(aQueueTableOffset) );
	}

	inline virtual ExecutionContext * popFrom(ListOfExecutionContext & aQueue)
	{
		return( StrategyPop::popFrom( aQueue ) );
	}


	////////////////////////////////////////////////////////////////////////////
	// TOP WAITING BEHAVIOR API
	////////////////////////////////////////////////////////////////////////////

	inline virtual ExecutionContext * top()
	{
		return( topFrom(mQueueCache.nonempty() ? mQueueCache : mQueue) );
	}

	inline virtual ExecutionContext * top(avm_uint8_t aQueueTableOffset)
	{
		return( topFrom( mQueueTable[ (aQueueTableOffset < mQueueCount) ?
				aQueueTableOffset : mQueueCount ] ) );
	}

	inline virtual ExecutionContext * topFrom(ListOfExecutionContext & aQueue)
	{
		return( StrategyPop::topFrom( aQueue ) );
	}

};


} /* namespace sep */

#endif /* FAM_QUEUE_WAITINGSTRATEGY_H_ */
