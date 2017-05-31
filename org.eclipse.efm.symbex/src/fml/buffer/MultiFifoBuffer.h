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


class MultiFifoBuffer : public BaseBufferQueue
{

	AVM_DECLARE_CLONABLE_CLASS( MultiFifoBuffer )


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	MultiFifoBuffer(InstanceOfBuffer * aBuffer)
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
	inline virtual bool push(const Message & aMsg)
	{
		if( size() < capacity() )
		{
			mMessages.push_back(aMsg);

			return( true );
		}

		return( false );
	}


	inline virtual bool top(const Message & aMsg)
	{
		if( nonempty() )
		{
			mMessages.front() = aMsg;

			return( true );
		}

		return( false );
	}

	inline virtual const Message & top() const
	{
		if( nonempty() )
		{
			return( mMessages.front() );
		}

		return( Message::_NULL_ );
	}

	inline virtual const Message & top(avm_size_t mid,
			const RuntimeID & aReceiverRID = RuntimeID::REF_NULL) const
	{
		ListOfMessage::const_iterator it = mMessages.begin();
		ListOfMessage::const_iterator itEnd = mMessages.end();
		for( ; it != itEnd ; ++it )
		{
			if( (*it).isCompatible(mid, aReceiverRID) )
			{
				return( *it );
			}
		}

		return( Message::_NULL_ );
	}


	/**
	 * contains
	 * uncontains
	 */
	inline virtual bool contains(ListOfInstanceOfPort & aSignalTrace,
			const RuntimeID & aReceiverRID = RuntimeID::REF_NULL) const
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


	inline virtual bool uncontains(ListOfInstanceOfPort & aSignalTrace,
			const RuntimeID & aReceiverRID = RuntimeID::REF_NULL) const
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
	inline virtual Message pop()
	{
		if( nonempty() )
		{
			Message aMsg = mMessages.front();

			mMessages.pop_front();

			return( aMsg );
		}

		return( Message::_NULL_ );
	}


	Message pop(avm_size_t mid,
			const RuntimeID & aReceiverRID = RuntimeID::REF_NULL)
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


	inline virtual void popBefore(const RuntimeID & aReceiverRID)
	{
		ListOfMessage::iterator it = mMessages.begin();
		for( ; it != mMessages.end() ; )
		{
			if( (*it).isCompatible(aReceiverRID) )
			{
				it = mMessages.erase( it );
			}
			else
			{
				++it;
			}
		}
	}

	inline virtual void popBefore(const ListOfInstanceOfPort & ieComs,
			const RuntimeID & aReceiverRID = RuntimeID::REF_NULL)
	{
		ListOfMessage::iterator it = mMessages.begin();
		for( ; it != mMessages.end() ; )
		{
			if( (*it).isCompatible(aReceiverRID) )
			{
				if( (*it).isCompatible(ieComs) )
				{
					break;
				}
				else
				{
					it = mMessages.erase( it );
				}
			}
			else
			{
				++it;
			}
		}
	}

	inline virtual void popBefore(const ListOfSizeT & ieComs,
			const RuntimeID & aReceiverRID = RuntimeID::REF_NULL)
	{
		ListOfMessage::iterator it = mMessages.begin();
		for( ; it != mMessages.end() ; )
		{
			if( (*it).isCompatible(aReceiverRID) )
			{
				if( (*it).isCompatible(ieComs) )
				{
					break;
				}
				else
				{
					it = mMessages.erase( it );
				}
			}
			else
			{
				++it;
			}
		}
	}


	/**
	 * copyTo
	 * restore
	 */
	inline virtual void copyTo(BaseBufferForm & aBuffer) const
	{
		ListOfMessage::const_iterator it = mMessages.begin();
		ListOfMessage::const_iterator itEnd = mMessages.end();
		for( ; it != itEnd ; ++it )
		{
			aBuffer.push( *it );
		}
	}

	inline virtual void restore(ListOfMessage & listOfMessage)
	{
		listOfMessage.splice( mMessages );

		mMessages.splice( listOfMessage );
	}

};


} /* namespace sep */

#endif /* MULTIFIFOBUFFER_H_ */
