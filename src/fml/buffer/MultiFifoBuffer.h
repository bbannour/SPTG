/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 3 févr. 2015
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef MULTIFIFOBUFFER_H_
#define MULTIFIFOBUFFER_H_

#include <fml/buffer/BaseBufferQueue.h>

namespace sep
{


class MultiFifoBuffer final : public BaseBufferQueue
{

	AVM_DECLARE_CLONABLE_CLASS( MultiFifoBuffer )


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	MultiFifoBuffer(const InstanceOfBuffer & aBuffer)
	: BaseBufferQueue(CLASS_KIND_T( MultiFifoBuffer ), aBuffer)
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	MultiFifoBuffer(const MultiFifoBuffer & aMultiFifo )
	: BaseBufferQueue( aMultiFifo )
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

		return( Message::nullref() );
	}

	inline virtual const Message & top(std::size_t mid,
			const RuntimeID & aReceiverRID = RuntimeID::nullref()) const override
	{
		ListOfMessage::const_iterator itMessage = mMessages.begin();
		ListOfMessage::const_iterator endMessage = mMessages.end();
		for( ; itMessage != endMessage ; ++itMessage )
		{
			if( (*itMessage).isCompatible(mid, aReceiverRID) )
			{
				return( *itMessage );
			}
		}

		return( Message::nullref() );
	}


	/**
	 * contains
	 * uncontains
	 */
	inline virtual bool contains(ListOfInstanceOfPort & aSignalTrace,
			const RuntimeID & aReceiverRID = RuntimeID::nullref()) const override
	{
		ListOfInstanceOfPort::const_iterator itSignal = aSignalTrace.begin();
		ListOfInstanceOfPort::const_iterator endSignal = aSignalTrace.end();
		ListOfMessage::const_iterator itMessage = mMessages.begin();
		ListOfMessage::const_iterator endMessage = mMessages.end();
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
			const RuntimeID & aReceiverRID = RuntimeID::nullref()) const override
	{
		ListOfInstanceOfPort::iterator itSignal = aSignalTrace.begin();
		ListOfInstanceOfPort::iterator endSignal = aSignalTrace.end();
		ListOfMessage::const_iterator itMessage = mMessages.begin();
		ListOfMessage::const_iterator endMessage = mMessages.end();
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
			Message aMsg = mMessages.front();

			mMessages.pop_front();

			return( aMsg );
		}

		return( Message::nullref() );
	}


	inline virtual Message pop(std::size_t mid,
			const RuntimeID & aReceiverRID = RuntimeID::nullref()) override
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

		return( Message::nullref() );
	}

	inline virtual void pop(std::size_t mid, List< Message > & messages,
			const RuntimeID & aReceiverRID = RuntimeID::nullref()) override
	{
		if( nonempty() )
		{
			Message aMsg = mMessages.front();
			if( aMsg.isCompatible(mid, aReceiverRID) )
			{
				mMessages.pop_front();

				messages.append( aMsg );
			}
		}
	}

	// Due to [-Woverloaded-virtual=]
	using BaseBufferQueue::pop;


	inline virtual void popBefore(const RuntimeID & aReceiverRID) override
	{
		ListOfMessage::iterator itMessage = mMessages.begin();
		for( ; itMessage != mMessages.end() ; )
		{
			if( (*itMessage).isCompatible(aReceiverRID) )
			{
				itMessage = mMessages.erase( itMessage );
			}
			else
			{
				++itMessage;
			}
		}
	}

	inline virtual void popBefore(const ListOfInstanceOfPort & ieComs,
			const RuntimeID & aReceiverRID = RuntimeID::nullref()) override
	{
		ListOfMessage::iterator itMessage = mMessages.begin();
		for( ; itMessage != mMessages.end() ; )
		{
			if( (*itMessage).isCompatible(aReceiverRID) )
			{
				if( (*itMessage).isCompatible(ieComs) )
				{
					break;
				}
				else
				{
					itMessage = mMessages.erase( itMessage );
				}
			}
			else
			{
				++itMessage;
			}
		}
	}

	inline virtual void popBefore(const ListOfSizeT & ieComs,
			const RuntimeID & aReceiverRID = RuntimeID::nullref()) override
	{
		ListOfMessage::iterator itMessage = mMessages.begin();
		for( ; itMessage != mMessages.end() ; )
		{
			if( (*itMessage).isCompatible(aReceiverRID) )
			{
				if( (*itMessage).isCompatible(ieComs) )
				{
					break;
				}
				else
				{
					itMessage = mMessages.erase( itMessage );
				}
			}
			else
			{
				++itMessage;
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


} /* namespace sep */

#endif /* MULTIFIFOBUFFER_H_ */
