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
#ifndef EXECUTIONQUEUE_H_
#define EXECUTIONQUEUE_H_

#include  <famcore/api/AbstractProcessorUnit.h>
#include "WaitingStrategy.h"

#include <collection/Typedef.h>

#include <fml/runtime/ExecutionContext.h>
#include <sew/SymbexControllerEventManager.h>

#include <stack>


namespace sep
{

class AbstractProcessorUnit;
class ExecutionContext;
class SymbexControllerUnitManager;


class ExecutionQueue :
		public AutoRegisteredProcessorUnit< ExecutionQueue >,
		public IHandlerEventDestroyCtx
{

	AVM_DECLARE_CLONABLE_CLASS( ExecutionQueue )

	/**
	 * MAIN PROCESSOR FACTORY
	 * for automatic registration in the processor repository
	 * the [ [ FULLY ] QUALIFIED ] NAME ID
	 */
	AVM_INJECT_AUTO_REGISTER_QUALIFIED_ID_KEY_3(
			"symbex.queue",
			"avm::processor.EXECUTION_QUEUE",
			"avm::core.EXECUTION_QUEUE" )
	// end registration


public:
	/**
	 * TYPEDEF
	 */
	typedef std::uint16_t             ENUM_STRATEGY_T;

	enum
	{
		STRATEGY_UNDEFINED            = 0x0000,

		// Basic Strategy Family
		STRATEGY_BFS                  = 0x0001,

		STRATEGY_DFS                  = 0x0002,

		STRATEGY_RFS                  = 0x0004,
		STRATEGY_XFS                  = 0x0008,

		STRATEGY_BEST                 = 0x0010,
		STRATEGY_FIRST                = 0x0020,
		STRATEGY_LAST                 = 0x0040,

		STRATEGY_ORDER                = 0x0080,

		STRATEGY_FAMILY_BASIC         = STRATEGY_BFS   | STRATEGY_DFS
		                              | STRATEGY_RFS   | STRATEGY_XFS
		                              | STRATEGY_BEST  | STRATEGY_ORDER
		                              | STRATEGY_FIRST | STRATEGY_LAST,

		// for popTo ReadyQueue
		STRATEGY_ALL                  = 0x0100,

		STRATEGY_FAMILY_BASIC_ALL     = STRATEGY_FAMILY_BASIC
		                              | STRATEGY_ALL,


		// Block Strategy
		STRATEGY_BLOCK                = 0x0200,

		// Weight Strategy
		STRATEGY_WEIGHT               = 0x0400,

		// ALIAS
		STRATEGY_WEIGHT_ALL_BFS       = STRATEGY_WEIGHT
                                      | STRATEGY_ALL
                                      | STRATEGY_BFS
	};

	/**
	 * DEFAULT QUEUE COUNT
	 */
	static const std::uint8_t DEFAULT_QUEUE_COUNT = 8;


protected:
	/**
	 * ATTRIBUTES
	 */
	// les contextes qui attendent sagement qu'on les initialise afin
	// qu'ils puissent étre mis dans la waiting!!!!
	// Il n'y a pas de raison qu'on en traite qu'un seul à la fois!!!!!
	ListOfExecutionContext mInitQueue;

	////////////////////////////////////////////////////////////////////////////
	// the waiting queue strategy & behavour
	////////////////////////////////////////////////////////////////////////////
	// les contextes qui attendent sagement qu'on s'intéresse à eux pour passer
	// l'audition conduisant à l'exécution !!!
	WaitingStrategy * mWaitingStrategy;
	std::stack< WaitingStrategy * > mWaitingStrategyStack;

	// les contextes pres pour l'exécution: ils ont réussi l'audition des filtres...
	// Il n'y a pas de raison qu'on en traite qu'un seul à la fois!!!
	ListOfExecutionContext mReadyQueue;

	// les contextes mis en réserve volontairement par un processeur,
	// et pourraient faire l'objet d'une récupération futur....
	ListOfExecutionContext mReserveQueue;

	// les contextes ayant échoué à l'épreuve des filtres,
	// et pourraient faire l'objet d'une épreuve de récupération futur...
	ListOfExecutionContext mFailedQueue;

	// les contextes venant d'etre exécutés
	// Il n'y a pas de raison qu'on en traite qu'un seul à la fois!!!
	ListOfExecutionContext mResultQueue;

	// les contextes fils choisis pour aller dans la Waiting Queue...
	// Il n'y a pas de raison qu'on en traite qu'un seul à la fois!!!
	ListOfExecutionContext mAnteWaitingQueue;


	/**
	 * Strategy
	 * DFS | BFS | RFS
	 * BLOCK_??? | WEIGHT_??? | TARGET_FORMULA_???
	 * STRATEGY_ORDER
	 */
	ENUM_STRATEGY_T mStrategy;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ExecutionQueue(SymbexControllerUnitManager & aControllerUnitManager,
			const WObject * wfParameterObject = nullptr)
	: AutoRegisteredProcessorUnit( aControllerUnitManager ,
			wfParameterObject , PRECEDENCE_OF_MAIN_PROCESSOR),
	mInitQueue(),

	mWaitingStrategy( nullptr ),
	mWaitingStrategyStack( ),

	mReadyQueue(),

	mReserveQueue(),
	mFailedQueue(),

	mResultQueue(),

	mAnteWaitingQueue(),

	mStrategy( STRATEGY_DFS )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~ExecutionQueue();


	/**
	 * CONFIGURE
	 */
	virtual bool configureImpl() override;

	void configureWaitingBasicStrategy();

	void configureWaitingBasicStrategyAll();

	void configureWaitingBlockStrategy(
			std::size_t aBlockHeightPeriod, std::size_t aBlockWidthPeriod,
			std::size_t aBlockHeight, std::size_t aBlockWidth,
			std::size_t aHeightLimit, std::size_t aWidthLimit);

	void configureWaitingWeightStrategy(std::uint8_t maxWeight);
	void configureWaitingWeightStrategyAll(std::uint8_t maxWeight);


	/**
	 * RECONFIGURATION
	 */
	bool reconfigure(ENUM_STRATEGY_T newStrategy,
			std::uint8_t queueCount = DEFAULT_QUEUE_COUNT);

	bool reconfigureBlock(ENUM_STRATEGY_T newStrategy,
			std::size_t aBlockHeightPeriod, std::size_t aBlockWidthPeriod,
			std::size_t aBlockHeight, std::size_t aBlockWidth,
			std::size_t aHeightLimit, std::size_t aWidthLimit);


	/**
	 * REPORT TRACE
	 */

	inline virtual void reportSilent(OutStream & os) const override
	{
		// SILENT => NOTHING
	}

	inline virtual void reportMinimum(OutStream & os) const override
	{
		//!! NOTHING
	}

	virtual void reportDefault(OutStream & os) const override;


	/**
	 * GETTER - SETTER
	 * mInitQueue
	 */
	inline void appendInit(ExecutionContext * anEC)
	{
		mInitQueue.append(anEC);
	}

	inline void appendInit(const ListOfExecutionContext & listOfEC)
	{
		mInitQueue.append(listOfEC);
	}

	inline ListOfExecutionContext & getInitQueue()
	{
		return( mInitQueue );
	}

	inline bool hasInit() const
	{
		return( mInitQueue.nonempty() );
	}

	inline void traceInit(OutStream & os)
	{
		traceQueue(os, mInitQueue, "EXECUTION INIT QUEUE");
	}


	/**
	 * GETTER - SETTER
	 * mWaitingStrategy
	 */
	inline WaitingStrategy * getWaitingStrategy()
	{
		return( mWaitingStrategy );
	}

	inline WaitingStrategy & refWaitingStrategy()
	{
		return( *mWaitingStrategy );
	}

	inline bool hasWaitingStrategy() const
	{
		return( mWaitingStrategy != nullptr );
	}

	inline void setWaitingStrategy(WaitingStrategy * aWaitingStrategy)
	{
		mWaitingStrategy = aWaitingStrategy;
	}


	/**
	 * GETTER - SETTER
	 * mWaitingStrategy
	 * mWaitingStrategyStack
	 */
	bool pushWaitingStrategy(WaitingStrategy * aWaitingStrategy,
			bool spliceContainedFlag = true);

	bool popWaitingStrategy(bool spliceContainedFlag = true,
			bool destroyCurrentFlag = false);


	/**
	 * hasWork()
	 */
	inline bool hasWork() const
	{
		return( hasWaiting() || hasReady() );
	}

	/**
	 * GETTER - SETTER
	 * mWaitingQueue
	 */

	inline void clearWaiting()
	{
		mWaitingStrategy->clearQueueTable();
	}

	inline void getWaiting(ListOfExecutionContext & alisOfEC)
	{
		mWaitingStrategy->getQueueTable( alisOfEC );
	}

	inline ListOfExecutionContext & getWaitingQueue()
	{
		return( mWaitingStrategy->getQueue() );
	}

	inline ListOfExecutionContext & getWaitingQueueCache()
	{
		return( mWaitingStrategy->getCache() );
	}


	inline bool hasWaiting() const
	{
		return( mWaitingStrategy->hasWaiting() );
	}

	inline bool hasWaitingCache() const
	{
		return( mWaitingStrategy->getCache().nonempty() );
	}



	inline ExecutionContext * topWaiting()
	{
		return( mWaitingStrategy->top() );
	}

	inline ExecutionContext * popWaiting()
	{
		return( mWaitingStrategy->pop() );
	}

	inline void popWaiting2Ready()
	{
		mWaitingStrategy->popTo( mReadyQueue );
	}

	inline void pushWaitingCache(ExecutionContext * anEC)
	{
		mWaitingStrategy->pushCache( anEC );
	}

	inline void spliceWaitingCache(ListOfExecutionContext & listOfEC)
	{
		while( listOfEC.nonempty() )
		{
			mWaitingStrategy->pushCache( listOfEC.pop_first() );
		}
	}

	inline void pushWaiting(ExecutionContext * anEC)
	{
		mWaitingStrategy->push( anEC );
	}

	inline void pushWaiting(const ListOfExecutionContext & listOfEC)
	{
		mWaitingStrategy->push( listOfEC );
	}

	inline void pushInit2Waiting()
	{
		while( mInitQueue.nonempty() )
		{
			mWaitingStrategy->push( mInitQueue.pop_first() );
		}
	}


	inline void pushAnteWaiting()
	{
		mWaitingStrategy->smartPush( mAnteWaitingQueue );
		mAnteWaitingQueue.clear();
	}

	inline void smartPushWaiting(const ListOfExecutionContext & listOfEC)
	{
		mWaitingStrategy->smartPush( listOfEC );
	}


	inline std::size_t sizeWaiting()
	{
		return( mWaitingStrategy->sizeWaiting() );
	}


	inline void traceWaiting(OutStream & os)
	{
		mWaitingStrategy->trace(os, "EXECUTION WAITING QUEUE");
	}


	/**
	 * GETTER - SETTER
	 * mReadyQueue
	 */
	inline void appendReady(ExecutionContext * anEC)
	{
		mReadyQueue.append(anEC);
	}

	inline void appendReady(ListOfExecutionContext & listOfEC)
	{
		mReadyQueue.append(listOfEC);
	}

	inline void spliceReady(ListOfExecutionContext & listOfEC)
	{
		mReadyQueue.splice(listOfEC);
	}

	inline void clearReady()
	{
		mReadyQueue.clear();
	}

	inline ListOfExecutionContext & getReadyQueue()
	{
		return( mReadyQueue );
	}

	inline bool hasReady() const
	{
		return( mReadyQueue.nonempty() );
	}

	inline bool hasReadyWork() const
	{
		return( mReadyQueue.nonempty() );
	}


	inline void traceReady(OutStream & os)
	{
		traceQueue(os, mReadyQueue, "EXECUTION READY QUEUE");
	}


	/**
	 * GETTER - SETTER
	 * mReserveQueue
	 */
	inline void appendReserve(ExecutionContext * anEC)
	{
		mReserveQueue.append(anEC);
	}

	inline void appendReserve(ListOfExecutionContext & listOfEC)
	{
		mReserveQueue.append(listOfEC);
	}

	inline void spliceReserve(ListOfExecutionContext & listOfEC)
	{
		mReserveQueue.splice(listOfEC);
	}

	inline ListOfExecutionContext & getReserveQueue()
	{
		return( mReserveQueue );
	}

	inline bool hasReserve() const
	{
		return( mReserveQueue.nonempty() );
	}


	inline void traceReserve(OutStream & os)
	{
		traceQueue(os, mReserveQueue, "EXECUTION LAST CHANCE QUEUE");
	}


	/**
	 * GETTER - SETTER
	 * mFailedQueue
	 */
	inline void appendFailed(ExecutionContext * anEC)
	{
		mFailedQueue.append(anEC);
	}

	inline void appendFailed(ListOfExecutionContext & listOfEC)
	{
		mFailedQueue.append(listOfEC);
	}

	inline void spliceFailed(ListOfExecutionContext & listOfEC)
	{
		mFailedQueue.splice(listOfEC);
	}

	inline ListOfExecutionContext & getFailedQueue()
	{
		return( mFailedQueue );
	}

	inline bool hasFailed() const
	{
		return( mFailedQueue.nonempty() );
	}


	inline void traceFailed(OutStream & os)
	{
		traceQueue(os, mFailedQueue, "EXECUTION FAILED QUEUE");
	}


	/**
	 * GETTER - SETTER
	 * mResultQueue
	 */
	inline void appendResult(ExecutionContext * anEC)
	{
		mResultQueue.append(anEC);
	}

	inline void appendResult(ListOfExecutionContext & listOfEC)
	{
		mResultQueue.append(listOfEC);
	}

	inline void spliceResult(ListOfExecutionContext & listOfEC)
	{
		mResultQueue.splice(listOfEC);
	}

	inline ListOfExecutionContext & getResultQueue()
	{
		return( mResultQueue );
	}

	inline bool hasResult() const
	{
		return( mResultQueue.nonempty() );
	}


	inline void traceResult(OutStream & os)
	{
		traceQueue(os, mResultQueue, "EXECUTION RESULT QUEUE");
	}


	/**
	 * GETTER - SETTER
	 * mAnteWaitingQueue
	 */
	inline void appendAnteWaiting(ExecutionContext * anEC)
	{
		mAnteWaitingQueue.append(anEC);
	}

	inline void appendAnteWaiting(ListOfExecutionContext & listOfEC)
	{
		mAnteWaitingQueue.append(listOfEC);
	}

	inline void spliceAnteWaiting(ListOfExecutionContext & listOfEC)
	{
		mAnteWaitingQueue.splice(listOfEC);
	}

	inline ListOfExecutionContext & getAnteWaitingQueue()
	{
		return( mAnteWaitingQueue );
	}

	inline bool hasAnteWaiting() const
	{
		return( mAnteWaitingQueue.nonempty() );
	}


	inline void traceAnteWaiting(OutStream & os)
	{
		traceQueue(os, mAnteWaitingQueue, "EXECUTION ANTE WAITING QUEUE");
	}


	/**
	 * TRACE Queue
	 */
	static void traceQueue(OutStream & os, ListOfExecutionContext & aQueue,
			const std::string & aMessage);


	/**
	 * IHandlerEventDestroyCtx API
	 * Destroy Execution Context
	 */
	inline virtual void handleEventDestroyCtx(ExecutionContext * anEC) override
	{
		removeFailed(anEC);
		removeInit(anEC);
		removeWaiting(anEC);
		removeReady(anEC);
		removeReserve(anEC);
		removeResult(anEC);
		removeAnteWaiting(anEC);
	}

	inline void removeFailed(ExecutionContext * anEC)
	{
		getFailedQueue().remove(anEC);
	}

	inline void removeInit(ExecutionContext * anEC)
	{
		getInitQueue().remove(anEC);
	}

	inline void removeWaiting(ExecutionContext * anEC)
	{
		mWaitingStrategy->remove(anEC);
	}

	inline void removeReady(ExecutionContext * anEC)
	{
		getReadyQueue().remove(anEC);
	}

	inline void removeReserve(ExecutionContext * anEC)
	{
		getReserveQueue().remove(anEC);
	}

	inline void removeResult(ExecutionContext * anEC)
	{
		getResultQueue().remove(anEC);
	}

	inline void removeAnteWaiting(ExecutionContext * anEC)
	{
		getAnteWaitingQueue().remove(anEC);
	}




	/**
	 * HEURISTIC
	 * BLOCK_DFS strategy
	 */
	ExecutionContext * pop_BLOCK_DFS();
	void push_BLOCK_DFS(ExecutionContext * anEC);
	bool resetWaiting_BLOCK();


	/**
	 * HEURISTIC
	 * BLOCK_BFS strategy
	 */
	ExecutionContext * pop_BLOCK_BFS();
	void push_BLOCK_BFS(ExecutionContext * anEC);


	/**
	 * HEURISTIC
	 * BLOCK_BFS strategy
	 */
	ExecutionContext * pop_BLOCK_XFS();
	void push_BLOCK_XFS(ExecutionContext * anEC);


	/**
	 * HEURISTIC
	 * ORDER strategy
	 */
	ExecutionContext * pop_ORDER();
	void push_ORDER(ExecutionContext * anEC);


	/**
	 * HEURISTIC
	 * TARGET_FORMULA strategy
	 */
	ExecutionContext * pop_TARGET_FORMULA();


	////////////////////////////////////////////////////////////////////////////
	// PROCESSOR RESET  API
	////////////////////////////////////////////////////////////////////////////

	inline virtual void resetQueues()
	{
		clearReady();

		clearWaiting();
	}

	inline virtual void resetQueues(ListOfExecutionContext & readyContexts,
			ListOfExecutionContext & waitingContexts)
	{
		readyContexts.splice( mReadyQueue );

		mWaitingStrategy->flushQueueTable( waitingContexts );
	}

	////////////////////////////////////////////////////////////////////////////
	// PROCESSOR REQUEST API
	////////////////////////////////////////////////////////////////////////////

	/**
	 * STOP  | RELEASE
	 * RESET | RESTART | CONTINUE
	 * REQUEUE_WAITING | REQUEUE_RESERVE
	 * HEURISTIC | GOAL_ACHIEVED
	 */
	inline virtual void handleRequestStop() override
	{
		clearReady();

		clearWaiting();
	}

	inline virtual void handleRequestRelease() override
	{
		//!! NOTHING
	}


	inline virtual void handleRequestReset() override
	{
		//!! NOTHING
	}

	inline virtual void handleRequestRestart() override
	{
		//!! NOTHING
	}

	inline virtual void handleRequestContinue() override
	{
		//!! NOTHING
	}


	inline void handleRequestRequeueWaiting(AbstractProcessorUnit * aRequestor)
	{
		mWaitingStrategy->handleRequestRequeueWaiting(aRequestor);
	}

	inline void handleRequestRequeueReserve(AbstractProcessorUnit * aRequestor)
	{
		mWaitingStrategy->handleRequestRequeueReserve(aRequestor, getReserveQueue());
	}


	/**
	 * Serialization
	 */
	std::string strStrategy() const;

	inline void toStreamWaiting(OutStream & os) const
	{
		mWaitingStrategy->toStream(os);
	}

	virtual void toStream(OutStream & os) const override;

	virtual void toStream(const ListOfExecutionContext & aQueue, OutStream & os) const;

};


}

#endif /*EXECUTIONQUEUE_H_*/
