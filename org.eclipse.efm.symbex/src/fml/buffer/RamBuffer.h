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
#ifndef RAMBUFFER_H_
#define RAMBUFFER_H_

#include <fml/buffer/BaseBufferForm.h>


#include <fml/runtime/Message.h>


namespace sep
{


class RuntimeID;



class RamBuffer : public BaseBufferForm
{

	AVM_DECLARE_CLONABLE_CLASS( RamBuffer )


protected:
	/*
	 * ATTRIBUTES
	 */
	Message mMessage;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	RamBuffer(InstanceOfBuffer * aBuffer)
	: BaseBufferForm(CLASS_KIND_T( RamBuffer ), aBuffer),
	mMessage( )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	RamBuffer(const RamBuffer & aRam)
	: BaseBufferForm( aRam ),
	mMessage( aRam.mMessage )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Other
	 */
	RamBuffer(class_kind_t aClassKind, InstanceOfBuffer * aBuffer)
	: BaseBufferForm(aClassKind, aBuffer),
	mMessage( )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~RamBuffer()
	{
		//!! NOTHING
	}


	////////////////////////////////////////////////////////////////////////////
	// BUFFER MANAGEMENT API
	////////////////////////////////////////////////////////////////////////////
	/**
	 * emptiness
	 * size
	 */
	inline virtual bool empty() const
	{
		return( mMessage.invalid() );
	}

	inline virtual bool nonempty() const
	{
		return( mMessage.valid() );
	}

	inline virtual bool singleton()const
	{
		return( mMessage.valid() );
	}

	inline virtual bool populated()const
	{
		return( false );
	}

	inline virtual bool full() const
	{
		return( mMessage.valid() );
	}

	virtual avm_size_t size() const
	{
		return( mMessage.valid() ? 1 : 0 );
	}

	/**
	 * Comparison
	 * operator==
	 */
	inline virtual bool equals(const BaseBufferForm & aBuffer) const
	{
		return( (this == &aBuffer)
				|| (aBuffer.is< RamBuffer >()
					&& mMessage.equals(
							aBuffer.to< RamBuffer >()->mMessage ) ) );
	}

	/**
	 * clear
	 * resize
	 */
	inline virtual void clear()
	{
		mMessage.destroy();
	}


	virtual void resize(avm_size_t newSize)
	{
		// NOTHING
	}

	inline virtual void resize(avm_size_t newSize, const Message & aMsg)
	{
		if( mMessage.invalid() )
		{
			mMessage = aMsg;
		}
	}


	/**
	 * push
	 * top
	 */
	inline virtual bool push(const Message & aMsg)
	{
		mMessage = aMsg;

		return( true );
	}


	inline virtual bool top(const Message & aMsg)
	{
		mMessage = aMsg;

		return( true );
	}

	inline virtual const Message & top() const
	{
		return( mMessage );
	}

	inline virtual const Message & top(avm_size_t mid,
			const RuntimeID & aReceiverRID = RuntimeID::REF_NULL) const
	{
		if( nonempty() && mMessage.isCompatible(mid, aReceiverRID) )
		{
			return( mMessage );
		}

		return( Message::_NULL_ );
	}


	/**
	 * contains
	 * uncontains
	 */
	inline virtual bool contains(avm_size_t mid,
			const RuntimeID & aReceiverRID = RuntimeID::REF_NULL) const
	{
		return( nonempty() && mMessage.isCompatible(mid, aReceiverRID) );
	}

	inline virtual bool contains(InstanceOfPort * aSignal,
			const RuntimeID & aReceiverRID = RuntimeID::REF_NULL) const
	{
		return( nonempty() && mMessage.isCompatible(aSignal, aReceiverRID) );
	}


	inline virtual bool contains(ListOfInstanceOfPort & aSignalTrace,
			const RuntimeID & aReceiverRID = RuntimeID::REF_NULL) const
	{
		return( aSignalTrace.singleton() &&
				contains(aSignalTrace.first(), aReceiverRID) );
	}

	inline virtual bool uncontains(ListOfInstanceOfPort & aSignalTrace,
			const RuntimeID & aReceiverRID = RuntimeID::REF_NULL) const
	{
		if( aSignalTrace.nonempty() &&
			contains(aSignalTrace.first(), aReceiverRID) )
		{
			aSignalTrace.pop_first();
		}

		return( aSignalTrace.nonempty() );
	}


	/**
	 * pop
	 */
	inline virtual Message pop()
	{
		return( mMessage );
	}


	inline virtual Message pop(avm_size_t mid,
			const RuntimeID & aReceiverRID = RuntimeID::REF_NULL)
	{
		if( nonempty() && mMessage.isCompatible(mid, aReceiverRID) )
		{
			return( mMessage );
		}

		return( Message::_NULL_ );
	}


	inline virtual void popBefore(const RuntimeID & aReceiverRID)
	{
		if( mMessage.isCompatible(aReceiverRID) )
		{
			clear();
		}
	}

	inline virtual void popBefore(const ListOfInstanceOfPort & ieComs,
			const RuntimeID & aReceiverRID = RuntimeID::REF_NULL)
	{
		if( mMessage.isCompatible(aReceiverRID) )
		{
			if( not mMessage.isCompatible(ieComs) )
			{
				clear();
			}
		}
	}

	inline virtual void popBefore(const ListOfSizeT & ieComs,
			const RuntimeID & aReceiverRID = RuntimeID::REF_NULL)
	{
		if( mMessage.isCompatible(aReceiverRID) )
		{
			if( not mMessage.isCompatible(ieComs) )
			{
				clear();
			}
		}
	}


	/**
	 * remove
	 * copyTo
	 * restore
	 */
	inline virtual void remove(InstanceOfPort * aSignal)
	{
		if( mMessage.valid() &&
			mMessage.isSignal(aSignal) )
		{
			mMessage.destroy();
		}
	}

	inline virtual void copyTo(BaseBufferForm & aBuffer) const
	{
		if( mMessage.valid() )
		{
			aBuffer.push( mMessage );
		}
	}

	inline virtual void restore(ListOfMessage & listOfMessage)
	{
		if( listOfMessage.nonempty() )
		{
			mMessage = listOfMessage.back();
		}
	}


	/**
	 ***************************************************************************
	 * SERIALIZATION
	 ***************************************************************************
	 */
	virtual void toStream(OutStream & os) const;

	virtual void toFscn(OutStream & os, const RuntimeID & aRID,
			const BaseBufferForm * prevBuf = NULL) const;

};


}

#endif /*RAMBUFFER_H_*/
