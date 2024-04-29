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
#ifndef FIFOBUFFER_H_
#define FIFOBUFFER_H_

#include <fml/buffer/BaseBufferQueue.h>

namespace sep
{


class FifoBuffer : public BaseBufferQueue
{

	AVM_DECLARE_CLONABLE_CLASS( FifoBuffer )


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	FifoBuffer(const InstanceOfBuffer & aBuffer)
	: BaseBufferQueue(CLASS_KIND_T( FifoBuffer ), aBuffer)
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	FifoBuffer(const FifoBuffer & aFifo )
	: BaseBufferQueue( aFifo )
	{
		//!! NOTHING
	}


	////////////////////////////////////////////////////////////////////////////
	// BUFFER MANAGEMENT API
	////////////////////////////////////////////////////////////////////////////
	/**
	 * push
	 * top
	 */
	inline virtual bool push(const Message & aMsg) override
	{
		if( size() < capacity() )
		{
			mMessages.push_back(aMsg);

			return( true );
		}

		return( false );
	}


	inline virtual bool top(const Message & aMsg) override
	{
		if( nonempty() )
		{
			mMessages.front() = aMsg;

			return( true );
		}

		return( false );
	}

	inline virtual const Message & top() const override
	{
		if( nonempty() )
		{
			return( mMessages.front() );
		}

		return( Message::_NULL_ );
	}

	inline virtual const Message & top(std::size_t mid,
			const RuntimeID & aReceiverRID = RuntimeID::REF_NULL) const override
	{
		if( nonempty()
			&& mMessages.front().isCompatible(mid, aReceiverRID) )
		{
			return( mMessages.front() );
		}

		return( Message::_NULL_ );
	}


	/**
	 * contains
	 * uncontains
	 */
	inline virtual bool contains(ListOfInstanceOfPort & aSignalTrace,
			const RuntimeID & aReceiverRID = RuntimeID::REF_NULL) const override
	{
		ListOfInstanceOfPort::const_iterator itSignal = aSignalTrace.begin();
		ListOfInstanceOfPort::const_iterator endSignal = aSignalTrace.end();
		ListOfMessage::const_iterator it = mMessages.begin();
		ListOfMessage::const_iterator itEnd = mMessages.end();
		for( ; (it != itEnd) && (itSignal != endSignal) ; ++it )
		{
			if( (*it).isCompatible(*itSignal, aReceiverRID) )
			{
				++itSignal;
			}
		}

		return( itSignal == endSignal );
	}

	// Due to [-Woverloaded-virtual=]
	using BaseBufferQueue::contains;


	inline virtual bool uncontains(ListOfInstanceOfPort & aSignalTrace,
			const RuntimeID & aReceiverRID = RuntimeID::REF_NULL) const override
	{
		ListOfInstanceOfPort::iterator itSignal = aSignalTrace.begin();
		ListOfInstanceOfPort::iterator endSignal = aSignalTrace.end();
		ListOfMessage::const_iterator it = mMessages.begin();
		ListOfMessage::const_iterator itEnd = mMessages.end();
		for( ; (it != itEnd) && (itSignal != endSignal) ; ++it )
		{
			if( (*it).isCompatible(*itSignal, aReceiverRID) )
			{
				itSignal = aSignalTrace.erase( itSignal );
			}
		}

		return( aSignalTrace.nonempty() );
	}


	/**
	 * pop
	 */
	inline virtual Message pop() override
	{
		if( nonempty() )
		{
			Message aMsg = mMessages.front();
			mMessages.pop_front();

			return( aMsg );
		}

		return( Message::_NULL_ );
	}


	inline virtual Message pop(std::size_t mid,
			const RuntimeID & aReceiverRID = RuntimeID::REF_NULL) override
	{
		if( nonempty() )
		{
			Message aMsg = mMessages.front();
			if( aMsg.isCompatible(mid, aReceiverRID) )
			{
				mMessages.pop_front();

				return( aMsg );
			}
		}

		return( Message::_NULL_ );
	}

	inline virtual void pop(std::size_t mid, List< Message > & messages,
			const RuntimeID & aReceiverRID = RuntimeID::REF_NULL) override
	{
		if( nonempty() )
		{
			Message aMsg = mMessages.front();
			if( aMsg.isCompatible(mid, aReceiverRID) )
			{
				mMessages.pop_front();

				messages.append( aMsg);
			}
		}
	}

	// Due to [-Woverloaded-virtual=]
	using BaseBufferQueue::pop;


	inline virtual void popBefore(const RuntimeID & aReceiverRID) override
	{
		while( nonempty() && mMessages.front().isCompatible(aReceiverRID) )
		{
			mMessages.pop_front();
		}
	}

	inline virtual void popBefore(const ListOfInstanceOfPort & ieComs,
			const RuntimeID & aReceiverRID = RuntimeID::REF_NULL) override
	{
		while( nonempty() && mMessages.front().isCompatible(aReceiverRID) )
		{
			if( mMessages.front().isCompatible(ieComs) )
			{
				break;
			}
			else
			{
				mMessages.pop_front();
			}
		}
	}

	inline virtual void popBefore(const ListOfSizeT & ieComs,
			const RuntimeID & aReceiverRID = RuntimeID::REF_NULL) override
	{
		while( nonempty() && mMessages.front().isCompatible(aReceiverRID) )
		{
			if( mMessages.front().isCompatible(ieComs) )
			{
				break;
			}
			else
			{
				mMessages.pop_front();
			}
		}
	}


	/**
	 * copyTo
	 * restore
	 */
	inline virtual void copyTo(BaseBufferForm & aBuffer) const override
	{
		for( const auto & itMessage : mMessages )
		{
			aBuffer.push( itMessage );
		}
	}

	inline virtual void restore(ListOfMessage & listOfMessage) override
	{
		listOfMessage.splice( mMessages );

		mMessages.splice( listOfMessage );
	}

};


}

#endif /*FIFOBUFFER_H_*/
