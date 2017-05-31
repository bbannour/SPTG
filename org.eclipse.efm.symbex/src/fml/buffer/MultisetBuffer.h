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
#ifndef MULTISETBUFFER_H_
#define MULTISETBUFFER_H_

#include <fml/buffer/BaseBufferQueue.h>

namespace sep
{


class MultisetBuffer : public BaseBufferQueue
{

	AVM_DECLARE_CLONABLE_CLASS( MultisetBuffer )


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	MultisetBuffer(InstanceOfBuffer * aBuffer)
	: BaseBufferQueue(CLASS_KIND_T( MultisetBuffer ), aBuffer)
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	MultisetBuffer(const MultisetBuffer & aMultiset )
	: BaseBufferQueue( aMultiset )
	{
		//!! NOTHING
	}


	/**
	 * BUFFER MANAGEMENT
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
			mMessages.back() = aMsg;

			return( true );
		}

		return( false );
	}

	inline virtual const Message & top() const
	{
		if( nonempty() )
		{
			return( mMessages.back() );
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
				return( (*it) );
			}
		}

		return( Message::_NULL_ );
	}



	inline virtual Message pop()
	{
		if( nonempty() )
		{
			Message aMsg = mMessages.pop_last();

			return( aMsg );
		}

		return( Message::_NULL_ );
	}


	inline virtual Message pop(avm_size_t mid,
			const RuntimeID & aReceiverRID = RuntimeID::REF_NULL)
	{
		ListOfMessage::iterator it = mMessages.begin();
		ListOfMessage::iterator itEnd = mMessages.end();
		for( ; it != itEnd ; ++it )
		{
			if( (*it).isCompatible(mid, aReceiverRID) )
			{
				Message aMsg = (*it);

				mMessages.erase(it);

				return( aMsg );
			}
		}

		return( Message::_NULL_ );
	}


	inline virtual void popBefore(const RuntimeID & aReceiverRID)
	{
		remove(aReceiverRID);
	}

	inline virtual void popBefore(const ListOfInstanceOfPort & ieComs,
			const RuntimeID & aReceiverRID = RuntimeID::REF_NULL)
	{
		ListOfMessage::const_iterator it = mMessages.begin();
		ListOfMessage::const_iterator itEnd = mMessages.end();
		for( ; it != itEnd ; ++it )
		{
			if( (*it).isCompatible(ieComs, aReceiverRID) )
			{
				return;
			}
		}

		remove(aReceiverRID);
	}

	inline virtual void popBefore(const ListOfSizeT & ieComs,
			const RuntimeID & aReceiverRID = RuntimeID::REF_NULL)
	{
		ListOfMessage::const_iterator it = mMessages.begin();
		ListOfMessage::const_iterator itEnd = mMessages.end();
		for( ; it != itEnd ; ++it )
		{
			if( (*it).isCompatible(ieComs, aReceiverRID) )
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
		mMessages.splice( listOfMessage );
	}


};

}

#endif /*MULTISETBUFFER_H_*/
