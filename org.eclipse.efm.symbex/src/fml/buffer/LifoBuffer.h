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
#ifndef LIFOBUFFER_H_
#define LIFOBUFFER_H_

#include <fml/buffer/BaseBufferQueue.h>

namespace sep
{


class LifoBuffer : public BaseBufferQueue
{

	AVM_DECLARE_CLONABLE_CLASS( LifoBuffer )


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	LifoBuffer(const InstanceOfBuffer & aBuffer)
	: BaseBufferQueue(CLASS_KIND_T( LifoBuffer ), aBuffer)
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	LifoBuffer(const LifoBuffer & aLifo )
	: BaseBufferQueue( aLifo )
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
			mMessages.back() = aMsg;

			return( true );
		}

		return( false );
	}

	inline virtual const Message & top() const override
	{
		if( nonempty() )
		{
			return( mMessages.back() );
		}

		return( Message::_NULL_ );
	}

	inline virtual const Message & top(std::size_t mid,
			const RuntimeID & aReceiverRID = RuntimeID::REF_NULL) const override
	{
		if( nonempty() && mMessages.back().isCompatible(mid, aReceiverRID) )
		{
			return( mMessages.back() );
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
		ListOfMessage::const_reverse_iterator itMessage = mMessages.rbegin();
		ListOfMessage::const_reverse_iterator endMessage = mMessages.rend();
		for( ; (itMessage != endMessage) && (itSignal != endSignal) ; ++itMessage )
		{
			if( (*itMessage).isCompatible(*itSignal, aReceiverRID) )
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
		ListOfMessage::const_reverse_iterator itMessage = mMessages.rbegin();
		ListOfMessage::const_reverse_iterator endMessage = mMessages.rend();
		for( ; (itMessage != endMessage) && (itSignal != endSignal) ; ++itMessage )
		{
			if( (*itMessage).isCompatible(*itSignal, aReceiverRID) )
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
			Message aMsg = mMessages.pop_last();

			return( aMsg );
		}

		return( Message::_NULL_ );
	}


	inline virtual Message pop(std::size_t mid,
			const RuntimeID & aReceiverRID = RuntimeID::REF_NULL) override
	{
		if( nonempty() )
		{
			Message aMsg = mMessages.back();
			if( aMsg.isCompatible(mid, aReceiverRID) )
			{
				mMessages.pop_back();

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
			Message aMsg = mMessages.back();
			if( aMsg.isCompatible(mid, aReceiverRID) )
			{
				mMessages.pop_back();

				messages.append( aMsg );
			}
		}
	}

	// Due to [-Woverloaded-virtual=]
	using BaseBufferQueue::pop;



	inline virtual void popBefore(const RuntimeID & aReceiverRID) override
	{
		while( nonempty() && mMessages.back().isCompatible(aReceiverRID) )
		{
			mMessages.pop_back();
		}
	}

	inline virtual void popBefore(const ListOfInstanceOfPort & ieComs,
			const RuntimeID & aReceiverRID = RuntimeID::REF_NULL) override
	{
		while( nonempty() && mMessages.back().isCompatible(aReceiverRID) )
		{
			if( mMessages.back().isCompatible(ieComs) )
			{
				break;
			}
			else
			{
				mMessages.pop_back();
			}
		}
	}

	inline virtual void popBefore(const ListOfSizeT & ieComs,
			const RuntimeID & aReceiverRID = RuntimeID::REF_NULL) override
	{
		while( nonempty() && mMessages.back().isCompatible(aReceiverRID) )
		{
			if( mMessages.back().isCompatible(ieComs) )
			{
				break;
			}
			else
			{
				mMessages.pop_back();
			}
		}
	}


	/**
	 * copyTo
	 * restore
	 */
	inline virtual void copyTo(BaseBufferForm & aBuffer) const override
	{
		ListOfMessage::const_reverse_iterator itMessage = mMessages.rbegin();
		ListOfMessage::const_reverse_iterator endMessage = mMessages.rend();
		for(  ; itMessage != endMessage ; ++itMessage )
		{
			aBuffer.push( *itMessage );
		}
	}

	inline virtual void restore(ListOfMessage & listOfMessage) override
	{
		while( listOfMessage.nonempty() )
		{
			mMessages.push_back( listOfMessage.back() );

			listOfMessage.pop_back();
		}
	}

};


}

#endif /*LIFOBUFFER_H_*/
