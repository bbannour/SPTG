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
#ifndef BASEBUFFERFORM_H_
#define BASEBUFFERFORM_H_

#include <common/Element.h>

#include <common/AvmPointer.h>

#include <collection/Typedef.h>

#include <fml/executable/InstanceOfBuffer.h>
#include <fml/executable/InstanceOfPort.h>

#include <fml/runtime/Message.h>

#include <fml/runtime/RuntimeID.h>


namespace sep
{


class RuntimeID;


class BaseBufferForm :
		public Element ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( BaseBufferForm )
{

protected:
	/**
	 * ATTRIBUTE
	 */
	InstanceOfBuffer * mBufferIntance;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BaseBufferForm(class_kind_t aClassKind, InstanceOfBuffer * aBuffer)
	: Element( aClassKind ),
	mBufferIntance( aBuffer )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 * Abstract pur
	 */
	BaseBufferForm(const BaseBufferForm & aBuffer)
	: Element( aBuffer ),
	mBufferIntance( aBuffer.mBufferIntance )
	{
		//!! NOTHING
	}



	/**
	 * DESTRUCTOR
	 */
	virtual ~BaseBufferForm()
	{
		//!! NOTHING
	}


	/**
	 * CLONE
	 */
	virtual BaseBufferForm * clone() const = 0;


	////////////////////////////////////////////////////////////////////////////
	// BUFFER MANAGEMENT API
	////////////////////////////////////////////////////////////////////////////
	/**
	 * emptiness
	 * size
	 */
	virtual bool empty() const = 0;

	virtual bool nonempty() const = 0;

	virtual bool singleton() const = 0;

	virtual bool populated() const = 0;

	virtual bool full() const = 0;

	virtual avm_size_t size() const = 0;

	/**
	 * Comparison
	 * operator==
	 */
	virtual bool equals(const BaseBufferForm & aBuffer) const = 0;

	/**
	 * clear
	 * resize
	 */
	virtual void clear() = 0;

	virtual void resize(avm_size_t newSize) = 0;
	virtual void resize(avm_size_t newSize, const Message & aMsg) = 0;

	/**
	 * push
	 * top
	 */
	virtual bool push(const Message & aMsg) = 0;

	virtual bool top(const Message & aMsg) = 0;

	virtual const Message & top() const = 0;
	virtual const Message & top(avm_size_t mid,
			const RuntimeID & aReceiverRID
					= RuntimeID::REF_NULL) const = 0;

	inline virtual bool isTop(avm_size_t mid,
			const RuntimeID & aReceiverRID
					= RuntimeID::REF_NULL) const
	{
		return( top(mid, aReceiverRID).valid() );
	}

	/**
	 * contains
	 * uncontains
	 */
	virtual bool contains(avm_size_t mid,
			const RuntimeID & aReceiverRID
					= RuntimeID::REF_NULL) const = 0;

	virtual bool contains(InstanceOfPort * aSignal,
			const RuntimeID & aReceiverRID
					= RuntimeID::REF_NULL) const = 0;

	virtual bool contains(ListOfInstanceOfPort & aSignalTrace,
			const RuntimeID & aReceiverRID
					= RuntimeID::REF_NULL) const = 0;

	virtual bool uncontains(ListOfInstanceOfPort & aSignalTrace,
			const RuntimeID & aReceiverRID
					= RuntimeID::REF_NULL) const = 0;

	/**
	 * pop
	 */
	virtual Message pop() = 0;

	virtual Message pop(avm_size_t mid,
			const RuntimeID & aReceiverRID = RuntimeID::REF_NULL) = 0;


	virtual void popBefore(const RuntimeID & aReceiverRID) = 0;

	virtual void popBefore(const ListOfInstanceOfPort & ieComs,
			const RuntimeID & aReceiverRID = RuntimeID::REF_NULL) = 0;

	virtual void popBefore(const ListOfSizeT & ieComs,
			const RuntimeID & aReceiverRID = RuntimeID::REF_NULL) = 0;


	/**
	 * remove
	 * copyTo
	 * restore
	 */
	virtual void remove(InstanceOfPort * aPort) = 0;

	virtual void copyTo(BaseBufferForm & aBuffer) const = 0;

	virtual void restore(ListOfMessage & listOfMessage) = 0;


	/**
	 * Serialize
	 */
	virtual void toFscn(OutStream & os, const RuntimeID & aRID,
			const BaseBufferForm * prevBuf = NULL) const = 0;


	/**
	 * GETTER - SETTER
	 * theInstance
	 */
	inline InstanceOfBuffer * getInstance() const
	{
		return( mBufferIntance );
	}

	inline bool hasInstance() const
	{
		return( mBufferIntance != NULL );
	}

};


}

#endif /*BASEBUFFERFORM_H_*/
