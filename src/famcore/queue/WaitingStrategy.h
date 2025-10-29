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

#include  <famcore/api/AbstractProcessorUnit.h>


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
	std::uint8_t mQueueCount;
	ListOfExecutionContext * mQueueTable;
	std::uint8_t tOffset;

	static const std::uint8_t QUEUE_CACHE = 0;
	static const std::uint8_t QUEUE_OTHER = 1;

	ListOfExecutionContext & mQueueCache;
	ListOfExecutionContext & mQueue;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	WaitingStrategy(std::uint8_t queueCount = 1)
	: //mWaitingBasicStrategy( nullptr ),
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
		return( nullptr );
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
	 * GETTER
	 * mQueueCount
	 */
	inline std::uint8_t getQueueCount() const
	{
		return( mQueueCount );
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


	inline void flushQueueTable(ListOfExecutionContext & listOfEC)
	{
		for( tOffset = 0 ; tOffset <= mQueueCount ; ++tOffset )
		{
			if( mQueueTable[ tOffset ].nonempty() )
			{
				listOfEC.splice( mQueueTable[ tOffset ] );
			}
		}
	}

	inline void flushQueueTable(
			ListOfExecutionContext & listOfEC, std::uint8_t tOffsetMax)
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


	inline std::uint8_t flushPriorQueueTable(ListOfExecutionContext & listOfEC)
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

	inline std::uint8_t flushPriorQueueTable(ListOfExecutionContext & listOfEC,
			std::uint8_t anOffsetMin, std::uint8_t tOffsetMax)
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

	inline bool hasWaiting(std::uint8_t tOffsetMax)
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


	inline std::size_t sizeWaiting() const
	{
		std::size_t wsize = 0;
		for( std::size_t tOffset = 0 ; tOffset <= mQueueCount ; ++tOffset )
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

		for( const auto & itQueueEC : aQueue )
		{
			itQueueEC->traceDefault(os);
		}
		os << DECR_INDENT;
	}

	inline void trace(OutStream & os, const std::string & aMessage)
	{
		for( std::size_t tOffset = 0 ; tOffset <= mQueueCount ; ++tOffset )
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

		for( std::size_t tOffset = 0 ; tOffset <= mQueueCount ; ++tOffset )
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
		for( const auto & itQueueEC : aQueue )
		{
			itQueueEC->traceDefault(os);

		}
	}



	////////////////////////////////////////////////////////////////////////////
	// PUSH WAITING BEHAVIOR API
	////////////////////////////////////////////////////////////////////////////

	/**
	 * PUSH
	 */
	virtual void push(ExecutionContext * anEC) = 0;

	inline virtual void push(const ListOfExecutionContext & listOfEC)
	{
		for( const auto & itQueueEC : listOfEC )
		{
			push( itQueueEC );
		}
	}


	virtual void push(std::uint8_t aQueueTableOffset,
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

	inline virtual void splice(std::uint8_t aQueueTableOffset,
			ListOfExecutionContext & listOfEC)
	{
		mQueueTable[ (aQueueTableOffset < mQueueCount) ?
				aQueueTableOffset : mQueueCount ].splice( listOfEC );
	}


	////////////////////////////////////////////////////////////////////////////
	// PUSH ANTE WAITING BEHAVIOR API
	////////////////////////////////////////////////////////////////////////////

	virtual void smartPush(const ListOfExecutionContext & childEC) = 0;

	virtual void smartPush(std::uint8_t aQueueTableOffset,
			ListOfExecutionContext & childEC) = 0;

	virtual void smartPush(ListOfExecutionContext & aQueue,
			ListOfExecutionContext & childEC) = 0;


	////////////////////////////////////////////////////////////////////////////
	// POP WAITING BEHAVIOR API
	////////////////////////////////////////////////////////////////////////////

	virtual ExecutionContext * pop() = 0;

	virtual void popTo(ListOfExecutionContext & aReadyQueue) = 0;

	virtual ExecutionContext * pop(std::uint8_t aQueueTableOffset) = 0;

	virtual void popTo(std::uint8_t aQueueTableOffset,
			ListOfExecutionContext & aReadyQueue) = 0;

	virtual ExecutionContext * popFrom(ListOfExecutionContext & aQueue) = 0;


	////////////////////////////////////////////////////////////////////////////
	// TOP WAITING BEHAVIOR API
	////////////////////////////////////////////////////////////////////////////

	virtual ExecutionContext * top() = 0;

	virtual ExecutionContext * top(std::uint8_t aQueueTableOffset) = 0;

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
		std::uint8_t weight = anEC->getWeight();

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

struct ExecutionContextIteratorFIFO
{
	typedef ListOfExecutionContext::const_iterator const_ec_iterator;

	inline static const_ec_iterator begin_ec(
			const ListOfExecutionContext & listOfEC)
	{
		return( listOfEC.begin() );
	}

	inline static const_ec_iterator end_ec(
			const ListOfExecutionContext & listOfEC)
	{
		return( listOfEC.end() );
	}
};


struct  ExecutionContextIteratorLIFO
{
	typedef ListOfExecutionContext::const_reverse_iterator const_ec_iterator;

	inline static const_ec_iterator begin_ec(
			const ListOfExecutionContext & listOfEC)
	{
		return( listOfEC.rbegin() );
	}

	inline static const_ec_iterator end_ec(
			const ListOfExecutionContext & listOfEC)
	{
		return( listOfEC.rend() );
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

		return( nullptr );
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
		return( nullptr );
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
		return( nullptr );
	}

};



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// ABSTRACT WAITING STRATEGY
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

template< class StrategyPush , class ExecutionContextIterator , class StrategyPop >
class WaitingStrategyImpl :
		public WaitingStrategy,
		public ExecutionContextIterator
{

public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	WaitingStrategyImpl(std::uint8_t queueCount = 1)
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
	inline virtual void push(ExecutionContext * anEC) override
	{
		push( mQueue , anEC );
	}

	inline virtual void push(std::uint8_t aQueueTableOffset,
			ExecutionContext * anEC) override
	{
		push( mQueueTable[ (aQueueTableOffset < mQueueCount) ?
				aQueueTableOffset : mQueueCount ] , anEC );
	}

	inline virtual void push(ListOfExecutionContext & aQueue,
			ExecutionContext * anEC) override
	{
		StrategyPush::push( aQueue , anEC );
	}


	////////////////////////////////////////////////////////////////////////////
	// PUSH ANTE WAITING BEHAVIOR API
	////////////////////////////////////////////////////////////////////////////

	typename ExecutionContextIterator::const_ec_iterator itEC;
	typename ExecutionContextIterator::const_ec_iterator itEnd;


	inline virtual void smartPush(const ListOfExecutionContext & childEC) override
	{
		itEC = ExecutionContextIterator::begin_ec( childEC );
		itEnd = ExecutionContextIterator::end_ec( childEC );
		for( ; itEC != itEnd ; ++itEC )
		{
			push( *itEC );
		}
	}

	inline virtual void smartPush(std::uint8_t aQueueTableOffset,
			ListOfExecutionContext & childEC) override
	{
		itEC = ExecutionContextIterator::begin_ec( childEC );
		itEnd = ExecutionContextIterator::end_ec( childEC );
		for( ; itEC != itEnd ; ++itEC )
		{
			push( aQueueTableOffset , *itEC );
		}
	}

	inline virtual void smartPush(ListOfExecutionContext & aQueue,
			ListOfExecutionContext & childEC) override
	{
		itEC = ExecutionContextIterator::begin_ec( childEC );
		itEnd = ExecutionContextIterator::end_ec( childEC );
		for( ; itEC != itEnd ; ++itEC )
		{
			push( aQueue , *itEC );
		}
	}


	////////////////////////////////////////////////////////////////////////////
	// POP WAITING BEHAVIOR API
	////////////////////////////////////////////////////////////////////////////

	inline virtual ExecutionContext * pop() override
	{
		return( popFrom(mQueueCache.nonempty() ? mQueueCache : mQueue) );
	}

	virtual void popTo(ListOfExecutionContext & aReadyQueue) override
	{
		aReadyQueue.append( pop() );
	}

	inline virtual ExecutionContext * pop(
			std::uint8_t aQueueTableOffset) override
	{
		return( popFrom( mQueueTable[ (aQueueTableOffset < mQueueCount) ?
				aQueueTableOffset : mQueueCount ] ) );
	}

	virtual void popTo(std::uint8_t aQueueTableOffset,
			ListOfExecutionContext & aReadyQueue) override
	{
		aReadyQueue.append( pop(aQueueTableOffset) );
	}

	inline virtual ExecutionContext * popFrom(
			ListOfExecutionContext & aQueue) override
	{
		return( StrategyPop::popFrom( aQueue ) );
	}


	////////////////////////////////////////////////////////////////////////////
	// TOP WAITING BEHAVIOR API
	////////////////////////////////////////////////////////////////////////////

	inline virtual ExecutionContext * top() override
	{
		return( topFrom(mQueueCache.nonempty() ? mQueueCache : mQueue) );
	}

	inline virtual ExecutionContext * top(
			std::uint8_t aQueueTableOffset) override
	{
		return( topFrom( mQueueTable[ (aQueueTableOffset < mQueueCount) ?
				aQueueTableOffset : mQueueCount ] ) );
	}

	inline virtual ExecutionContext * topFrom(
			ListOfExecutionContext & aQueue) override
	{
		return( StrategyPop::topFrom( aQueue ) );
	}

};


} /* namespace sep */

#endif /* FAM_QUEUE_WAITINGSTRATEGY_H_ */
