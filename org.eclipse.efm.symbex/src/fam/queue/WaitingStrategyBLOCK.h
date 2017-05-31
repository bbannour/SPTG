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

#ifndef WAITINGSTRATEGYBLOCK_H_
#define WAITINGSTRATEGYBLOCK_H_

#include "WaitingStrategy.h"
#include "WaitingBasicStrategy.h"

#include <sew/Configuration.h>


namespace sep
{


template< class BasicStrategy >
class WaitingStrategyBLOCK  :  public BasicStrategy
{

protected:
	/**
	 * ATTRIBUTE
	 */
	Configuration & mConfiguration;

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	WaitingStrategyBLOCK(
			Configuration & aConfiguration, avm_uint8_t queueCount,
			avm_size_t aBlockHeightPeriod, avm_size_t aBlockWidthPeriod,
			avm_size_t aBlockHeight, avm_size_t aBlockWidth,
			avm_size_t aHeightLimit, avm_size_t aWidthLimit)
	: BasicStrategy( queueCount ),
	mConfiguration( aConfiguration ),
	mBlockHeightPeriod( aBlockHeightPeriod ),
	mBlockWidthPeriod( aBlockWidthPeriod ),

	mBlockHeight( aBlockHeight ),
	mBlockWidth( aBlockWidth ),

	mHeightLimit( aHeightLimit ),
	mWidthLimit( aWidthLimit ),

	mPushHeightMin( 0 ),
	mPushWidthMin( 0 ),

	mPushHeightMax( 0 ),
	mPushWidthMax( 0 )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~WaitingStrategyBLOCK()
	{
		//!! NOTHING
	}


	////////////////////////////////////////////////////////////////////////////
	// PUSH / PUSH#CHILD  API
	////////////////////////////////////////////////////////////////////////////

	void push(ExecutionContext * anEC)
	{
		if( (anEC->getHeight() <= mBlockHeight) &&
				(anEC->getWidth() <= mBlockWidth) )
		{
			BasicStrategy::push(BasicStrategy::mQueueCache, anEC);
		}
		else
		{
			BasicStrategy::push(BasicStrategy::mQueue, anEC);
		}

		// For algo optimization
		if( mPushHeightMax < anEC->getHeight() )
		{
			mPushHeightMax = anEC->getHeight();
		}
		if( mPushWidthMax < anEC->getWidth() )
		{
			mPushWidthMax = anEC->getWidth();
		}
	}

	////////////////////////////////////////////////////////////////////////////
	// POP / TOP  API
	////////////////////////////////////////////////////////////////////////////

	bool updateQueue()
	{
		mPushHeightMin = mPushHeightMax;
		mPushWidthMin  = mPushWidthMax;

		ListOfExecutionContext::iterator itEC = BasicStrategy::mQueue.begin();
		ListOfExecutionContext::iterator itEnd = BasicStrategy::mQueue.end();
		while( itEC != itEnd )
		{
			// For algo optimization
			if( mPushHeightMin > (*itEC)->getHeight() )
			{
				mPushHeightMin = (*itEC)->getHeight();
			}
			if( mPushWidthMin > (*itEC)->getWidth() )
			{
				mPushWidthMin = (*itEC)->getWidth();
			}

			if( ((*itEC)->getHeight() <= mBlockHeight) &&
					((*itEC)->getWidth() <= mBlockWidth) )
			{
				//BasicStrategy::push(BasicStrategy::mQueueCache, (*itEC));
				BasicStrategy::mQueueCache.push_back( *itEC );

				itEC = BasicStrategy::mQueue.erase(itEC);
			}
			else
			{
				++itEC;
			}
		}

		return( BasicStrategy::mQueueCache.nonempty() );
	}

	inline ExecutionContext * top()
	{
		if( BasicStrategy::mQueueCache.nonempty() )
		{
			return( BasicStrategy::topFrom( BasicStrategy::mQueueCache ) );
		}

		return( NULL );
	}


protected:
	/*ATTRIBUTES*/
	avm_size_t mBlockHeightPeriod;
	avm_size_t mBlockWidthPeriod;

	avm_size_t mBlockHeight;
	avm_size_t mBlockWidth;

	avm_size_t mHeightLimit;
	avm_size_t mWidthLimit;

	avm_size_t mPushHeightMin;
	avm_size_t mPushWidthMin;

	avm_size_t mPushHeightMax;
	avm_size_t mPushWidthMax;

};


#define NEXT_INCR(M, P)  (M + P - (M % P))




template< class BasicStrategyALL >
class WaitingStrategyBLOCK_ALL :
		public WaitingStrategyBLOCK< BasicStrategyALL >
{

private:
	/**
	 * TYPEDEF
	 */
	typedef WaitingStrategyBLOCK< BasicStrategyALL >  base_this_type;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	WaitingStrategyBLOCK_ALL(
			Configuration & aConfiguration, avm_uint8_t queueCount,
			avm_size_t aBlockHeightPeriod, avm_size_t aBlockWidthPeriod,
			avm_size_t aBlockHeight, avm_size_t aBlockWidth,
			avm_size_t aHeightLimit, avm_size_t aWidthLimit)
	: base_this_type(aConfiguration, queueCount,
			aBlockHeightPeriod, aBlockWidthPeriod,
			aBlockHeight, aBlockWidth, aHeightLimit, aWidthLimit)
	{
		//!! NOTHING
	}


	////////////////////////////////////////////////////////////////////////////
	// POP / TOP  API
	////////////////////////////////////////////////////////////////////////////

	ExecutionContext * pop()
	{
		return( NULL );
	}


	void popTo(ListOfExecutionContext & aReadyQueue)
	{
		static avm_size_t call_counter = 0;
		++call_counter;

		if( BasicStrategyALL::mQueueCache.nonempty() )
		{
			aReadyQueue.splice( BasicStrategyALL::mQueueCache );
		}
		else if( BasicStrategyALL::mQueue.nonempty() )
		{
			while( true )
			{
				// Recherche par block en BFS à partir de la hauteur courante
				while( (base_this_type::mBlockWidth < base_this_type::mWidthLimit) &&
						(base_this_type::mBlockWidth < base_this_type::mPushWidthMax) )
				{
					base_this_type::mBlockWidth = std::min(base_this_type::mWidthLimit,
								base_this_type::mBlockWidth + base_this_type::mBlockWidthPeriod);

					AVM_OS_COUT << "update mBlockWidth [" << call_counter << "] :> "
							<< "H<" << base_this_type::mBlockHeightPeriod << ">[ "
							<< base_this_type::mPushHeightMin << " , " << base_this_type::mPushHeightMax << " ]"
							<< " => height:" << base_this_type::mBlockHeight << " <---> "
							<< "W<" << base_this_type::mBlockWidthPeriod << ">[ "
							<< base_this_type::mPushWidthMin << " , " << base_this_type::mPushWidthMax << " ]"
							<< " => width:" << base_this_type::mBlockWidth << std::endl;

					if( base_this_type::updateQueue() )
					{
						aReadyQueue.splice( BasicStrategyALL::mQueueCache );
					}
				}

//				mConfiguration.saveTraceSpecification(AVM_OS_COUT);
//				mConfiguration.saveScenarii();

				// Recherche par block BFS à partir
				// d'une hauteur augmentée d'une taille de block
				if( (base_this_type::mPushHeightMin < base_this_type::mHeightLimit) &&
						(base_this_type::mPushWidthMin < base_this_type::mWidthLimit) )
				{
					base_this_type::mBlockHeight = std::min(base_this_type::mHeightLimit,
							NEXT_INCR(base_this_type::mPushHeightMin, base_this_type::mBlockHeightPeriod));

					base_this_type::mBlockWidth = std::min(base_this_type::mWidthLimit,
							NEXT_INCR( base_this_type::mPushWidthMin , base_this_type::mBlockWidthPeriod));

					AVM_OS_COUT << "update mBlockHeight[" << call_counter << "] :> "
							<< "H<" << base_this_type::mBlockHeightPeriod << ">[ "
							<< base_this_type::mPushHeightMin << " , " << base_this_type::mPushHeightMax << " ]"
							<< " => height:" << base_this_type::mBlockHeight << " <---> "
							<< "W<" << base_this_type::mBlockWidthPeriod << ">[ "
							<< base_this_type::mPushWidthMin << " , " << base_this_type::mPushWidthMax << " ]"
							<< " => width:" << base_this_type::mBlockWidth << std::endl;

					if( base_this_type::updateQueue() )
					{
						aReadyQueue.splice( BasicStrategyALL::mQueueCache );
					}
				}

				// Recherche par block DFS à partir
				// d'un nouveau périmètre doublé
				base_this_type::mBlockHeight = NEXT_INCR(base_this_type::mPushHeightMin, base_this_type::mBlockHeightPeriod);
				base_this_type::mBlockWidth  = NEXT_INCR(base_this_type::mPushWidthMin , base_this_type::mBlockWidthPeriod);

				base_this_type::mHeightLimit += base_this_type::mHeightLimit;
				base_this_type::mWidthLimit  += base_this_type::mWidthLimit;

				AVM_OS_COUT << "update mBlockLimit[" << call_counter << "] :> "
						<< "height:" << base_this_type::mHeightLimit
						<< " width:" << base_this_type::mWidthLimit
						<< "  ==>  reset mBlockSize :> "
						<< "H<" << base_this_type::mBlockHeightPeriod << ">[ "
						<< base_this_type::mPushHeightMin << " , " << base_this_type::mPushHeightMax << " ]"
						<< " => height:" << base_this_type::mBlockHeight << " <---> "
						<< "W<" << base_this_type::mBlockWidthPeriod << ">[ "
						<< base_this_type::mPushWidthMin << " , " << base_this_type::mPushWidthMax << " ]"
						<< " => width:" << base_this_type::mBlockWidth << std::endl;

				if( base_this_type::updateQueue() )
				{
					aReadyQueue.splice( BasicStrategyALL::mQueueCache );
				}
			}
		}
	}

};



class WaitingStrategyBLOCK_BFS :
		public WaitingStrategyBLOCK< WaitingBasicStrategyBFS >
{

private:
	/**
	 * TYPEDEF
	 */
	typedef WaitingStrategyBLOCK< WaitingBasicStrategyBFS >  base_this_type;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	WaitingStrategyBLOCK_BFS(
			Configuration & aConfiguration, avm_uint8_t queueCount,
			avm_size_t aBlockHeightPeriod, avm_size_t aBlockWidthPeriod,
			avm_size_t aBlockHeight, avm_size_t aBlockWidth,
			avm_size_t aHeightLimit, avm_size_t aWidthLimit)
	: base_this_type(aConfiguration, queueCount,
			aBlockHeightPeriod, aBlockWidthPeriod,
			aBlockHeight, aBlockWidth, aHeightLimit, aWidthLimit)
	{
		//!! NOTHING
	}


	////////////////////////////////////////////////////////////////////////////
	// POP / TOP  API
	////////////////////////////////////////////////////////////////////////////

	ExecutionContext * pop()
	{
		static avm_size_t call_counter = 0;
		++call_counter;

		if( WaitingBasicStrategyBFS::mQueueCache.nonempty() )
		{
			return( WaitingBasicStrategyBFS::popFrom(
					WaitingBasicStrategyBFS::mQueueCache) );
		}
		else if( WaitingBasicStrategyBFS::mQueue.nonempty() )
		{
			while( true )
			{
				// Recherche par block en BFS à partir de la hauteur courante
				while( (mBlockWidth < mWidthLimit) &&
						(mBlockWidth < mPushWidthMax) )
				{
					mBlockWidth = std::min(mWidthLimit,
								mBlockWidth + mBlockWidthPeriod);

					AVM_OS_COUT << "update mBlockWidth [" << call_counter << "] :> "
							<< "H<" << mBlockHeightPeriod << ">[ "
							<< mPushHeightMin << " , " << mPushHeightMax << " ]"
							<< " => height:" << mBlockHeight << " <---> "
							<< "W<" << mBlockWidthPeriod << ">[ "
							<< mPushWidthMin << " , " << mPushWidthMax << " ]"
							<< " => width:" << mBlockWidth << std::endl;

					if( updateQueue() )
					{
						return( WaitingBasicStrategyBFS::popFrom(
								WaitingBasicStrategyBFS::mQueueCache) );
					}
				}

//				mConfiguration.saveTraceSpecification(AVM_OS_COUT);
//				mConfiguration.saveScenarii();

				// Recherche par block BFS à partir
				// d'une hauteur augmentée d'une taille de block
				if( (mPushHeightMin < mHeightLimit) &&
						(mPushWidthMin < mWidthLimit) )
				{
					mBlockHeight = std::min(mHeightLimit,
							NEXT_INCR(mPushHeightMin, mBlockHeightPeriod));

					mBlockWidth = std::min(mWidthLimit,
							NEXT_INCR( mPushWidthMin , mBlockWidthPeriod));

					AVM_OS_COUT << "update mBlockHeight[" << call_counter << "] :> "
							<< "H<" << mBlockHeightPeriod << ">[ "
							<< mPushHeightMin << " , " << mPushHeightMax << " ]"
							<< " => height:" << mBlockHeight << " <---> "
							<< "W<" << mBlockWidthPeriod << ">[ "
							<< mPushWidthMin << " , " << mPushWidthMax << " ]"
							<< " => width:" << mBlockWidth << std::endl;

					if( updateQueue() )
					{
						return( WaitingBasicStrategyBFS::popFrom(
								WaitingBasicStrategyBFS::mQueueCache) );
					}
				}

				// Recherche par block DFS à partir
				// d'un nouveau périmètre doublé
				mBlockHeight = NEXT_INCR(mPushHeightMin, mBlockHeightPeriod);
				mBlockWidth  = NEXT_INCR(mPushWidthMin , mBlockWidthPeriod);

				mHeightLimit += mHeightLimit;
				mWidthLimit  += mWidthLimit;

				AVM_OS_COUT << "update mBlockLimit[" << call_counter << "] :> "
						<< "height:" << mHeightLimit
						<< " width:" << mWidthLimit
						<< "  ==>  reset mBlockSize :> "
						<< "H<" << mBlockHeightPeriod << ">[ "
						<< mPushHeightMin << " , " << mPushHeightMax << " ]"
						<< " => height:" << mBlockHeight << " <---> "
						<< "W<" << mBlockWidthPeriod << ">[ "
						<< mPushWidthMin << " , " << mPushWidthMax << " ]"
						<< " => width:" << mBlockWidth << std::endl;

				if( updateQueue() )
				{
					return( WaitingBasicStrategyBFS::popFrom(
							WaitingBasicStrategyBFS::mQueueCache) );
				}
			}
		}

		return( NULL );
	}

};




class WaitingStrategyBLOCK_DFS :
		public WaitingStrategyBLOCK< WaitingBasicStrategyDFS >
{

private:
	/**
	 * TYPEDEF
	 */
	typedef WaitingStrategyBLOCK< WaitingBasicStrategyDFS >  base_this_type;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	WaitingStrategyBLOCK_DFS(
			Configuration & aConfiguration, avm_uint8_t queueCount,
			avm_size_t aBlockHeightPeriod, avm_size_t aBlockWidthPeriod,
			avm_size_t aBlockHeight, avm_size_t aBlockWidth,
			avm_size_t aHeightLimit, avm_size_t aWidthLimit)
	: base_this_type(aConfiguration, queueCount,
			aBlockHeightPeriod, aBlockWidthPeriod,
			aBlockHeight, aBlockWidth, aHeightLimit, aWidthLimit)
	{
		//!! NOTHING
	}


	////////////////////////////////////////////////////////////////////////////
	// POP / TOP  API
	////////////////////////////////////////////////////////////////////////////

	ExecutionContext * pop()
	{
		static avm_size_t call_counter = 0;
		++call_counter;

		if( WaitingBasicStrategyDFS::mQueueCache.nonempty() )
		{
			return( WaitingBasicStrategyDFS::popFrom(
					WaitingBasicStrategyDFS::mQueueCache) );
		}
		else if( WaitingBasicStrategyDFS::mQueue.nonempty() )
		{
			while( true )
			{
				// Recherche par block en DFS à partir de la largeur courante
				while( (mBlockHeight < mHeightLimit) &&
						(mBlockHeight < mPushHeightMax) )
				{
					mBlockHeight = std::min(mHeightLimit,
								mBlockHeight + mBlockHeightPeriod);

					AVM_OS_COUT << "update mBlockHeight[" << call_counter << "] :> "
							<< "H<" << mBlockHeightPeriod << ">[ "
							<< mPushHeightMin << " , " << mPushHeightMax << " ]"
							<< " => height:" << mBlockHeight << " <---> "
							<< "W<" << mBlockWidthPeriod << ">[ "
							<< mPushWidthMin << " , " << mPushWidthMax << " ]"
							<< " => width:" << mBlockWidth << std::endl;

					if( updateQueue() )
					{
						return( WaitingBasicStrategyDFS::popFrom(
								WaitingBasicStrategyDFS::mQueueCache) );
					}
				}

//				mConfiguration.saveTraceSpecification(AVM_OS_COUT);
//				mConfiguration.saveScenarii();

				// Recherche par block DFS à partir
				// d'une largeur augmentée d'une taille de block
				if( (mPushWidthMin < mWidthLimit) &&
						(mPushHeightMin < mHeightLimit) )
				{
					mBlockHeight = std::min(mHeightLimit,
							NEXT_INCR(mPushHeightMin, mBlockHeightPeriod));

					mBlockWidth = std::min(mWidthLimit,
							NEXT_INCR( mPushWidthMin , mBlockWidthPeriod));

					AVM_OS_COUT << "update mBlockWidth [" << call_counter << "] :> "
							<< "H<" << mBlockHeightPeriod << ">[ "
							<< mPushHeightMin << " , " << mPushHeightMax << " ]"
							<< " => height:" << mBlockHeight << " <---> "
							<< "W<" << mBlockWidthPeriod << ">[ "
							<< mPushWidthMin << " , " << mPushWidthMax << " ]"
							<< " => width:" << mBlockWidth << std::endl;

					if( updateQueue() )
					{
						return( WaitingBasicStrategyDFS::popFrom(
								WaitingBasicStrategyDFS::mQueueCache) );
					}
				}

				// Recherche par block DFS à partir
				// d'un nouveau périmètre doublé
				else
				{
					mBlockHeight = NEXT_INCR(mPushHeightMin, mBlockHeightPeriod);
					mBlockWidth  = NEXT_INCR(mPushWidthMin , mBlockWidthPeriod);

					mHeightLimit += mHeightLimit;
					mWidthLimit  += mWidthLimit;

					AVM_OS_COUT << "update mBlockLimit[" << call_counter << "] :>"
							<< "height:" << mHeightLimit
							<< " width:" << mWidthLimit
							<< "  ==>  reset mBlockSize :> "
							<< "H<" << mBlockHeightPeriod << ">[ "
							<< mPushHeightMin << " , " << mPushHeightMax << " ]"
							<< " => height:" << mBlockHeight << " <---> "
							<< "W<" << mBlockWidthPeriod << ">[ "
							<< mPushWidthMin << " , " << mPushWidthMax << " ]"
							<< " => width:" << mBlockWidth << std::endl;

					if( updateQueue() )
					{
						return( WaitingBasicStrategyDFS::popFrom(
								WaitingBasicStrategyDFS::mQueueCache) );
					}
				}
			}
		}

		return( NULL );
	}

};



class WaitingStrategyBLOCK_RFS :
		public WaitingStrategyBLOCK< WaitingBasicStrategyRFS >
{

private:
	/**
	 * TYPEDEF
	 */
	typedef WaitingStrategyBLOCK< WaitingBasicStrategyRFS >  base_this_type;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	WaitingStrategyBLOCK_RFS(
			Configuration & aConfiguration, avm_uint8_t queueCount,
			avm_size_t aBlockHeightPeriod, avm_size_t aBlockWidthPeriod,
			avm_size_t aBlockHeight, avm_size_t aBlockWidth,
			avm_size_t aHeightLimit, avm_size_t aWidthLimit)
	: base_this_type(aConfiguration, queueCount,
			aBlockHeightPeriod, aBlockWidthPeriod,
			aBlockHeight, aBlockWidth, aHeightLimit, aWidthLimit)
	{
		//!! NOTHING
	}


	////////////////////////////////////////////////////////////////////////////
	// POP / TOP  API
	////////////////////////////////////////////////////////////////////////////

	ExecutionContext * pop()
	{
		static avm_size_t call_counter = 0;
		++call_counter;

		if( WaitingBasicStrategyRFS::mQueueCache.nonempty() )
		{
			return( WaitingBasicStrategyRFS::popFrom(
					WaitingBasicStrategyRFS::mQueueCache) );
		}
		else if( WaitingBasicStrategyRFS::mQueue.nonempty() )
		{
			while( true )
			{
				while( (mBlockHeight < mHeightLimit) ||
						(mBlockWidth < mWidthLimit) )
				{
					// Recherche par block RFS à partir d'un périmètre augmenté,
					//  d'une taille de block en hauteur et/ou en largeur
					mBlockHeight = std::min(mHeightLimit,
								mBlockHeight + mBlockHeightPeriod);

					mBlockWidth = std::min(mWidthLimit,
								mBlockWidth + mBlockWidthPeriod);

					AVM_OS_COUT << "update mBlockSize[" << call_counter << "] :> "
							<< "H[ " << mPushHeightMin << " , " << mPushHeightMax << " ]"
							<< " W[ " << mPushWidthMin << " , " << mPushWidthMax << " ]"
							<< "height:" << mBlockHeight
							<< " width:" << mBlockWidth << std::endl;

					if( updateQueue() )
					{
						return( WaitingBasicStrategyRFS::popFrom(
								WaitingBasicStrategyRFS::mQueueCache) );
					}
				}

//				mConfiguration.saveTraceSpecification(AVM_OS_COUT);
//				mConfiguration.saveScenarii();

				// Recherche par block RFS à partir d'un périmètre augmenté
				// d'une taille de block en hauteur et en largeur
				// et en doublant le périmètre limite
				mBlockHeight = mHeightLimit + mBlockHeightPeriod;
				mBlockWidth  = mWidthLimit  + mBlockWidthPeriod;

				mHeightLimit += mHeightLimit;
				mWidthLimit  += mWidthLimit;

				AVM_OS_COUT << "update mBlockLimit[" << call_counter << "] :> "
						<< "height:" << mHeightLimit
						<< " width:" << mWidthLimit
						<< "  ==>  reset mBlockSize :> "
						<< "H[ " << mPushHeightMin << " , " << mPushHeightMax << " ]"
						<< " => height:" << mBlockHeight << " <---> "
						<< "W[ " << mPushWidthMin << " , " << mPushWidthMax << " ]"
						<< " => width:" << mBlockWidth << std::endl;

				if( updateQueue() )
				{
					return( WaitingBasicStrategyRFS::popFrom(
							WaitingBasicStrategyRFS::mQueueCache) );
				}
			}
		}

		return( NULL );
	}

};



} /* namespace sep */
#endif /* WAITINGSTRATEGYBLOCK_H_ */
