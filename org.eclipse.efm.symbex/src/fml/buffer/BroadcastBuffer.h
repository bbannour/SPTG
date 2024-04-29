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
#ifndef BROADCASTBUFFER_H_
#define BROADCASTBUFFER_H_

#include <fml/buffer/RamBuffer.h>


namespace sep
{


class RuntimeID;


class BroadcastBuffer : public RamBuffer
{

	AVM_DECLARE_CLONABLE_CLASS( BroadcastBuffer )


protected:
	/*
	 * ATTRIBUTES
	 */
	Message mNextStepMessage;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BroadcastBuffer(const InstanceOfBuffer & aBuffer)
	: RamBuffer(CLASS_KIND_T( BroadcastBuffer ), aBuffer),
	mNextStepMessage( )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	BroadcastBuffer(const BroadcastBuffer & aBroadcast)
	: RamBuffer( aBroadcast ),
	mNextStepMessage( )
	{
		//!! NOTHING
	}


	/**
	 ***************************************************************************
	 * UPDATE ==> push( mNextStepMessage )
	 ***************************************************************************
	 */
	inline virtual void update()
	{
		mMessage.flush( mNextStepMessage );
	}


	/**
	 * BUFFER MANAGEMENT
	 */
	inline virtual bool push(const Message & aMsg) override
	{
		mNextStepMessage = aMsg;

		return( true );
	}

	inline virtual bool top(const Message & aMsg) override
	{
		mNextStepMessage = aMsg;

		return( true );
	}

	// Due to [-Woverloaded-virtual=]
	using RamBuffer::top;

	/**
	 ***************************************************************************
	 * SERIALIZATION
	 ***************************************************************************
	 */
	void toStream(OutStream & out) const override;

	virtual void toStreamValue(OutStream & out) const override;

	void toFscn(OutStream & out, const RuntimeID & aRID,
			const BaseBufferForm * prevBuf = nullptr) const override;

};


}

#endif /*BROADCASTBUFFER_H_*/
