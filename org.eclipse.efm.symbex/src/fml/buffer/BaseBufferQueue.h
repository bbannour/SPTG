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
#ifndef BASEBUFFERQUEUE_H_
#define BASEBUFFERQUEUE_H_

#include <fml/buffer/BaseBufferForm.h>
#include <collection/BFContainer.h>

#include <fml/runtime/Message.h>


namespace sep
{


class RuntimeID;


class BaseBufferQueue  :  public BaseBufferForm
{

public:
	/**
	 * TYPEDEF
	 */
	typedef ListOfMessage::const_iterator  const_iterator;

protected:
	/*
	 * ATTRIBUTE
	 */
	ListOfMessage mMessages;

	std::size_t mCapacity;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BaseBufferQueue(class_kind_t aClassKind, const InstanceOfBuffer & aBuffer)
	: BaseBufferForm(aClassKind, aBuffer),
	mMessages( ),
	mCapacity( aBuffer.getCapacity() )
	{
			//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	BaseBufferQueue(const BaseBufferQueue & aBuffer)
	: BaseBufferForm( aBuffer ),
	mMessages( aBuffer.mMessages ),
	mCapacity( aBuffer.mCapacity )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~BaseBufferQueue()
	{
		//!! NOTHING
	}


	/**
	 * GETTER - SETTER
	 * mMessages
	 */
	inline const_iterator beginMessages() const
	{
		return( mMessages.begin() );
	}

	inline const_iterator endMessages() const
	{
		return( mMessages.end() );
	}

	inline ListOfMessage & getMessages()
	{
		return( mMessages );
	}


	/**
	 * GETTER - SETTER
	 * mCapacity
	 */
	inline std::size_t capacity() const
	{
		return( mCapacity );
	}

	inline long realCapacity() const
	{
		return( (mCapacity == AVM_NUMERIC_MAX_SIZE_T)? -1 : mCapacity );
	}

	inline void setCapacity(long aCapacity)
	{
		mCapacity = (aCapacity < 0) ? AVM_NUMERIC_MAX_SIZE_T : aCapacity;
	}

	inline bool isFinite() const
	{
		return( mCapacity < AVM_NUMERIC_MAX_SIZE_T );
	}

	inline bool isInfinite() const
	{
		return( mCapacity == AVM_NUMERIC_MAX_SIZE_T );
	}


	/**
	 * Comparison
	 * operator==
	 */
	virtual bool equals(const BaseBufferForm & aBuffer) const override;


	////////////////////////////////////////////////////////////////////////////
	// BUFFER MANAGEMENT API
	////////////////////////////////////////////////////////////////////////////
	/**
	 * emptiness
	 * size
	 */
	inline virtual bool empty() const override
	{
		return( mMessages.empty() );
	}

	inline virtual bool nonempty() const override
	{
		return( mMessages.nonempty() );
	}

	inline virtual bool singleton() const override
	{
		return( mMessages.singleton() );
	}

	inline virtual bool populated() const override
	{
		return( mMessages.populated() );
	}

	inline virtual bool full() const override
	{
		return( size() == mCapacity );
	}

	inline virtual std::size_t size() const override
	{
		return( mMessages.size() );
	}

	/**
	 * clear
	 * resize
	 * remove
	 */
	inline virtual void clear() override
	{
		mMessages.clear();
	}

	inline virtual void resize(std::size_t newSize) override
	{
		if( mCapacity > newSize )
		{
			if( (mCapacity = size()) > newSize )
			{
				for( ; mCapacity > newSize ; --mCapacity )
				{
					pop();
				}
				return;
			}
		}
		mCapacity = newSize;
	}

	inline virtual void resize(std::size_t newSize, const Message & aMsg) override
	{
		if( mCapacity > newSize )
		{
			if( (mCapacity = size()) > newSize )
			{
				for( ; mCapacity > newSize ; --mCapacity )
				{
					pop();
				}
				return;
			}
		}
		else if( (mCapacity = size()) < newSize )
		{
			for( ; mCapacity < newSize ; ++mCapacity )
			{
				push(aMsg);
			}
		}

		mCapacity = newSize;
	}


	inline virtual void remove(InstanceOfPort * aSignal) override
	{
		ListOfMessage::iterator it = mMessages.begin();
		for( ; it != mMessages.end() ; )
		{
			if( (*it).isSignal(aSignal) )
			{
				it = mMessages.erase(it);
			}
			else
			{
				++it;
			}
		}
	}


	inline virtual void remove(const RuntimeID & aReceiverRID)
	{
		if( aReceiverRID.valid() )
		{
			ListOfMessage::iterator it = mMessages.begin();
			for( ; it != mMessages.end() ; )
			{
				if( (*it).isReceiver(aReceiverRID) )
				{
					it = mMessages.erase( it );
				}
				else
				{
					++it;
				}
			}
		}
		else
		{
			clear();
		}
	}



	/**
	 * contains
	 * uncontains
	 */
	inline virtual bool contains(std::size_t mid,
			const RuntimeID & aReceiverRID = RuntimeID::REF_NULL) const override
	{
		const_iterator it = mMessages.begin();
		const_iterator itEnd = mMessages.end();
		for( ; it != itEnd ; ++it )
		{
			if( (*it).isCompatible(mid, aReceiverRID) )
			{
				return( true );
			}
		}
		return( false );
	}


	inline virtual bool contains(InstanceOfPort * aSignal,
			const RuntimeID & aReceiverRID = RuntimeID::REF_NULL) const override
	{
		const_iterator it = mMessages.begin();
		const_iterator itEnd = mMessages.end();
		for( ; it != itEnd ; ++it )
		{
			if( (*it).isCompatible(aSignal, aReceiverRID) )
			{
				return( true );
			}
		}
		return( false );
	}


	inline virtual bool contains(ListOfInstanceOfPort & aSignalTrace,
			const RuntimeID & aReceiverRID = RuntimeID::REF_NULL) const override
	{
		for( const auto & itSignal : aSignalTrace )
		{
			if( not contains( itSignal , aReceiverRID ) )
			{
				return( false );
			}
		}

		return( true );
	}


	inline virtual bool uncontains(ListOfInstanceOfPort & aSignalTrace,
			const RuntimeID & aReceiverRID = RuntimeID::REF_NULL) const override
	{
		ListOfInstanceOfPort::iterator itSignal = aSignalTrace.begin();
		ListOfInstanceOfPort::iterator endSignal = aSignalTrace.end();
		for( ; itSignal != endSignal ; )
		{
			if( contains( *itSignal, aReceiverRID ) )
			{
				itSignal = aSignalTrace.erase( itSignal );
			}
		}

		return( aSignalTrace.nonempty() );
	}


	/**
	 * Serialization
	 */
	virtual void toStream(OutStream & out) const override;

	virtual void toStreamValue(OutStream & out) const override;

	virtual void toFscn(OutStream & out, const RuntimeID & aRID,
			const BaseBufferForm * prevBuf = nullptr) const override;

};


}

#endif /*BASEBUFFERQUEUE_H_*/
