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

#ifndef WAITINGSTRATEGYWEIGHT_H_
#define WAITINGSTRATEGYWEIGHT_H_

#include "WaitingStrategy.h"


namespace sep
{


template< class BasicStrategy >
class WaitingStrategyWEIGHT  :  public BasicStrategy
{

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	WaitingStrategyWEIGHT(avm_uint8_t queueCount)
	: BasicStrategy( queueCount ),
	mPushWeightMin( queueCount ),
	mPushWeightMax( 0 )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~WaitingStrategyWEIGHT()
	{
		//!! NOTHING
	}


	////////////////////////////////////////////////////////////////////////////
	// PUSH  API
	////////////////////////////////////////////////////////////////////////////

	inline void push(ExecutionContext * anEC)
	{
		BasicStrategy::tOffset = anEC->getWeight();

		BasicStrategy::push(BasicStrategy::tOffset, anEC);

		// For algo optimization
		if( mPushWeightMin > BasicStrategy::tOffset )
		{
			mPushWeightMin = BasicStrategy::tOffset;
		}
		if( mPushWeightMax < BasicStrategy::tOffset )
		{
			mPushWeightMax = BasicStrategy::tOffset;
		}
	}


	////////////////////////////////////////////////////////////////////////////
	// POP / TOP  API
	////////////////////////////////////////////////////////////////////////////

	inline ExecutionContext * pop()
	{
		for( ; mPushWeightMin <= mPushWeightMax ; ++mPushWeightMin )
		{
			if( BasicStrategy::mQueueTable[ mPushWeightMin ].nonempty() )
			{
				return( BasicStrategy::popFrom(
						BasicStrategy::mQueueTable[ mPushWeightMin ] ) );
			}
		}

//		for( BasicStrategy::tOffset = 0 ;
//				BasicStrategy::tOffset <= BasicStrategy::mQueueCount ;
//				++BasicStrategy::tOffset )
//		{
//			if( BasicStrategy::mQueueTable[ BasicStrategy::tOffset ].nonempty() )
//			{
//				return( BasicStrategy::pop(
//						BasicStrategy::mQueueTable[ BasicStrategy::tOffset ] ) );
//			}
//		}

		return( NULL );
	}


	inline virtual void popTo(ListOfExecutionContext & aReadyQueue)
	{
		for( ; mPushWeightMin <= mPushWeightMax ; ++mPushWeightMin )
		{
			if( BasicStrategy::mQueueTable[ mPushWeightMin ].nonempty() )
			{
				BasicStrategy::popTo(mPushWeightMin, aReadyQueue);

				break;
			}
		}
	}


	inline ExecutionContext * top()
	{
		for( ; mPushWeightMin <= mPushWeightMax ; ++mPushWeightMin )
		{
			if( BasicStrategy::mQueueTable[ mPushWeightMin ].nonempty() )
			{
				return( BasicStrategy::topFrom(
						BasicStrategy::mQueueTable[ mPushWeightMin ] ) );
			}
		}

		return( NULL );
	}


	////////////////////////////////////////////////////////////////////////////
	// PROCESSOR REQUEST API :> REQUEUE
	////////////////////////////////////////////////////////////////////////////

	void handleRequestRequeue(AbstractProcessorUnit * aRequestor)
	{
		aRequestor->handleRequestRequeueWaitingTable( *this,
				mPushWeightMin, mPushWeightMax );
	}




protected:
	/*ATTRIBUTES*/
	avm_uint8_t mPushWeightMin;
	avm_uint8_t mPushWeightMax;

};


} /* namespace sep */
#endif /* WAITINGSTRATEGYWEIGHT_H_ */
