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
#ifndef SETBUFFER_H_
#define SETBUFFER_H_

#include <fml/buffer/BaseBufferQueue.h>

namespace sep
{



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// BaseSetQueue for SetBuffer and MultisetBuffer
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


class BaseSetQueue : public BaseBufferQueue
{

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BaseSetQueue(class_kind_t aClassKind, const InstanceOfBuffer & aBuffer)
	: BaseBufferQueue(aClassKind, aBuffer)
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	BaseSetQueue(const BaseSetQueue & aBuffer )
	: BaseBufferQueue( aBuffer )
	{
		//!! NOTHING
	}


	/**
	 * BUFFER MANAGEMENT
	 */
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
				return( (*itMessage) );
			}
		}

		return( Message::nullref() );
	}


	inline virtual Message pop() override
	{
		if( nonempty() )
		{
			Message aMsg = mMessages.pop_last();

			return( aMsg );
		}

		return( Message::nullref() );
	}


	inline virtual Message pop(std::size_t mid,
			const RuntimeID & aReceiverRID = RuntimeID::nullref()) override
	{
		ListOfMessage::iterator itMessage = mMessages.begin();
		ListOfMessage::iterator endMessage = mMessages.end();
		for( ; itMessage != endMessage ; ++itMessage )
		{
			if( (*itMessage).isCompatible(mid, aReceiverRID) )
			{
				Message aMsg = (*itMessage);

				mMessages.erase(itMessage);

				return( aMsg );
			}
		}

		return( Message::nullref() );
	}

	inline virtual Message pop(std::size_t mid, std::size_t minOccurrence,
			const RuntimeID & aReceiverRID = RuntimeID::nullref()) override
	{
		std::size_t occurrence = 0;
		ListOfMessage::iterator itMessage = mMessages.begin();
		ListOfMessage::iterator endMessage = mMessages.end();
		for( ; itMessage != endMessage ; ++itMessage , ++occurrence )
		{
			if(  (occurrence >= minOccurrence)
				&& (*itMessage).isCompatible(mid, aReceiverRID) )
			{
				Message aMsg = (*itMessage);

				mMessages.erase(itMessage);

				return( aMsg );
			}
		}

		return( Message::nullref() );
	}


	inline virtual void pop(std::size_t mid, List< Message > & messages,
			const RuntimeID & aReceiverRID = RuntimeID::nullref()) override
	{
		ListOfMessage::iterator itMessage = mMessages.begin();
		ListOfMessage::iterator endMessage = mMessages.end();
		for( ; itMessage != endMessage ; )
		{
			if( (*itMessage).isCompatible(mid, aReceiverRID) )
			{
				messages.append( *itMessage );

				itMessage = mMessages.erase(itMessage);
			}
			else
			{
				++itMessage;
			}
		}
	}


	inline virtual void popBefore(const RuntimeID & aReceiverRID) override
	{
		remove(aReceiverRID);
	}

	inline virtual void popBefore(const ListOfInstanceOfPort & ieComs,
			const RuntimeID & aReceiverRID = RuntimeID::nullref()) override
	{
		for( const auto & itMessage : mMessages )
		{
			if( itMessage.isCompatible(ieComs, aReceiverRID) )
			{
				return;
			}
		}

		remove(aReceiverRID);
	}

	inline virtual void popBefore(const ListOfSizeT & ieComs,
			const RuntimeID & aReceiverRID = RuntimeID::nullref()) override
	{
		for( const auto & itMessage : mMessages )
		{
			if( itMessage.isCompatible(ieComs, aReceiverRID) )
			{
				return;
			}
		}

		remove(aReceiverRID);
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
		mMessages.splice( listOfMessage );
	}


};


////////////////////////////////////////////////////////////////////////////////
// SetBuffer
////////////////////////////////////////////////////////////////////////////////

class SetBuffer final : public BaseSetQueue
{

	AVM_DECLARE_CLONABLE_CLASS( SetBuffer )


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	SetBuffer(const InstanceOfBuffer & aBuffer)
	: BaseSetQueue(CLASS_KIND_T( SetBuffer ), aBuffer)
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	SetBuffer(const SetBuffer & aSet )
	: BaseSetQueue( aSet )
	{
		//!! NOTHING
	}


	/**
	 * BUFFER MANAGEMENT
	 */
	inline virtual bool push(const Message & aMsg) override
	{
		if( size() < capacity() )
		{
			// Assume that is a set
			for( const auto & itMessage : mMessages )
			{
				if( itMessage.equals(aMsg) )
				{
					return( true );
				}
			}

			mMessages.push_back(aMsg);

			return( true );
		}

		return( false );
	}

};


////////////////////////////////////////////////////////////////////////////////
// MultisetBuffer
////////////////////////////////////////////////////////////////////////////////

class MultisetBuffer final : public BaseSetQueue
{

	AVM_DECLARE_CLONABLE_CLASS( MultisetBuffer )


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	MultisetBuffer(const InstanceOfBuffer & aBuffer)
	: BaseSetQueue(CLASS_KIND_T( MultisetBuffer ), aBuffer)
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	MultisetBuffer(const MultisetBuffer & aMultiset )
	: BaseSetQueue( aMultiset )
	{
		//!! NOTHING
	}


	/**
	 * BUFFER MANAGEMENT
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

};


}

#endif /*SETBUFFER_H_*/
