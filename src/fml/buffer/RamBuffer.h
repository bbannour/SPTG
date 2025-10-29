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
	RamBuffer(const InstanceOfBuffer & aBuffer)
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
	RamBuffer(class_kind_t aClassKind, const InstanceOfBuffer & aBuffer)
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
	inline virtual bool empty() const override
	{
		return( mMessage.invalid() );
	}

	inline virtual bool nonempty() const override
	{
		return( mMessage.valid() );
	}

	inline virtual bool singleton() const override
	{
		return( mMessage.valid() );
	}

	inline virtual bool populated() const override
	{
		return( false );
	}

	inline virtual bool full() const override
	{
		return( mMessage.valid() );
	}

	virtual std::size_t size() const override
	{
		return( mMessage.valid() ? 1 : 0 );
	}

	/**
	 * Comparison
	 * operator==
	 */
	inline virtual bool equals(const BaseBufferForm & aBuffer) const override
	{
		return( (this == &aBuffer)
				|| (aBuffer.is< RamBuffer >()
					&& mMessage.equals(aBuffer.to< RamBuffer >().mMessage)) );
	}

	/**
	 * clear
	 * resize
	 */
	inline virtual void clear() override
	{
		mMessage.destroy();
	}


	virtual void resize(std::size_t newSize) override
	{
		// NOTHING
	}

	inline virtual void resize(std::size_t newSize, const Message & aMsg) override
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
	inline virtual bool push(const Message & aMsg) override
	{
		mMessage = aMsg;

		return( true );
	}


	inline virtual bool top(const Message & aMsg) override
	{
		mMessage = aMsg;

		return( true );
	}

	inline virtual const Message & top() const override
	{
		return( mMessage );
	}

	inline virtual const Message & top(std::size_t mid,
			const RuntimeID & aReceiverRID = RuntimeID::nullref()) const override
	{
		if( nonempty() && mMessage.isCompatible(mid, aReceiverRID) )
		{
			return( mMessage );
		}

		return( Message::nullref() );
	}


	/**
	 * contains
	 * uncontains
	 */
	inline virtual bool contains(std::size_t mid,
			const RuntimeID & aReceiverRID = RuntimeID::nullref()) const override
	{
		return( nonempty() && mMessage.isCompatible(mid, aReceiverRID) );
	}

	inline virtual bool contains(InstanceOfPort * aSignal,
			const RuntimeID & aReceiverRID = RuntimeID::nullref()) const override
	{
		return( nonempty() && mMessage.isCompatible(aSignal, aReceiverRID) );
	}


	inline virtual bool contains(ListOfInstanceOfPort & aSignalTrace,
			const RuntimeID & aReceiverRID = RuntimeID::nullref()) const override
	{
		return( aSignalTrace.singleton() &&
				contains(aSignalTrace.first(), aReceiverRID) );
	}

	inline virtual bool uncontains(ListOfInstanceOfPort & aSignalTrace,
			const RuntimeID & aReceiverRID = RuntimeID::nullref()) const override
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
	inline virtual Message pop() override
	{
		return( mMessage );
	}


	inline virtual Message pop(std::size_t mid,
			const RuntimeID & aReceiverRID = RuntimeID::nullref()) override
	{
		if( nonempty() && mMessage.isCompatible(mid, aReceiverRID) )
		{
			return( mMessage );
		}

		return( Message::nullref() );
	}

	inline virtual void pop(std::size_t mid, List< Message > & messages,
			const RuntimeID & aReceiverRID = RuntimeID::nullref()) override
	{
		if( nonempty() && mMessage.isCompatible(mid, aReceiverRID) )
		{
			messages.append( mMessage );
		}
	}

	// Due to [-Woverloaded-virtual=]
	using BaseBufferForm::pop;


	inline virtual void popBefore(const RuntimeID & aReceiverRID) override
	{
		if( mMessage.isCompatible(aReceiverRID) )
		{
			clear();
		}
	}

	inline virtual void popBefore(const ListOfInstanceOfPort & ieComs,
			const RuntimeID & aReceiverRID = RuntimeID::nullref()) override
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
			const RuntimeID & aReceiverRID = RuntimeID::nullref()) override
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
	inline virtual void remove(InstanceOfPort * aSignal) override
	{
		if( mMessage.valid() &&
			mMessage.isSignal(aSignal) )
		{
			mMessage.destroy();
		}
	}

	inline virtual void copyTo(BaseBufferForm & aBuffer) const override
	{
		if( mMessage.valid() )
		{
			aBuffer.push( mMessage );
		}
	}

	inline virtual void restore(ListOfMessage & listOfMessage) override
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
	virtual void toStream(OutStream & out) const override;

	virtual void toStreamValue(OutStream & out) const override;

	virtual void toFscn(OutStream & out, const RuntimeID & aRID,
			const BaseBufferForm * prevBuf = nullptr) const override;

};


}

#endif /*RAMBUFFER_H_*/
