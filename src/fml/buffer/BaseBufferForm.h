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

#include <collection/List.h>

#include <fml/executable/InstanceOfBuffer.h>
#include <fml/executable/InstanceOfPort.h>

#include <fml/runtime/Message.h>

#include <fml/runtime/RuntimeID.h>


namespace sep
{


class RuntimeID;


class BaseBufferForm : public Element ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( BaseBufferForm )
{

protected:
	/**
	 * ATTRIBUTE
	 */
	const InstanceOfBuffer & mBufferIntance;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BaseBufferForm(class_kind_t aClassKind, const InstanceOfBuffer & aBuffer)
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
	virtual BaseBufferForm * clone() const override = 0;


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

	virtual std::size_t size() const override = 0;

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

	virtual void resize(std::size_t newSize) = 0;
	virtual void resize(std::size_t newSize, const Message & aMsg) = 0;

	/**
	 * push
	 * top
	 */
	virtual bool push(const Message & aMsg) = 0;

	virtual bool top(const Message & aMsg) = 0;

	virtual const Message & top() const = 0;
	virtual const Message & top(std::size_t mid,
			const RuntimeID & aReceiverRID
					= RuntimeID::nullref()) const = 0;

	inline virtual bool isTop(std::size_t mid,
			const RuntimeID & aReceiverRID
					= RuntimeID::nullref()) const
	{
		return( top(mid, aReceiverRID).valid() );
	}

	/**
	 * contains
	 * uncontains
	 */
	virtual bool contains(std::size_t mid,
			const RuntimeID & aReceiverRID
					= RuntimeID::nullref()) const = 0;

	virtual bool contains(InstanceOfPort * aSignal,
			const RuntimeID & aReceiverRID
					= RuntimeID::nullref()) const = 0;

	virtual bool contains(ListOfInstanceOfPort & aSignalTrace,
			const RuntimeID & aReceiverRID
					= RuntimeID::nullref()) const = 0;

	virtual bool uncontains(ListOfInstanceOfPort & aSignalTrace,
			const RuntimeID & aReceiverRID
					= RuntimeID::nullref()) const = 0;

	/**
	 * pop
	 */
	virtual Message pop() = 0;

	virtual Message pop(std::size_t mid,
			const RuntimeID & aReceiverRID = RuntimeID::nullref()) = 0;

	inline virtual Message pop(std::size_t mid, std::size_t minOccurrence,
			const RuntimeID & aReceiverRID = RuntimeID::nullref())
	{
		return( pop(mid, aReceiverRID) );
	}

	virtual void pop(std::size_t mid, List< Message > & messages,
			const RuntimeID & aReceiverRID = RuntimeID::nullref()) = 0;


	virtual void popBefore(const RuntimeID & aReceiverRID) = 0;

	virtual void popBefore(const ListOfInstanceOfPort & ieComs,
			const RuntimeID & aReceiverRID = RuntimeID::nullref()) = 0;

	virtual void popBefore(const ListOfSizeT & ieComs,
			const RuntimeID & aReceiverRID = RuntimeID::nullref()) = 0;


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
	virtual void toStreamValue(OutStream & out) const = 0;

	inline std::string strValue() const
	{
		StringOutStream oss(AVM_STR_INDENT);

		toStreamValue( oss );

		return( oss.str() );
	}

	virtual void toFscn(OutStream & out, const RuntimeID & aRID,
			const BaseBufferForm * prevBuf = nullptr) const = 0;


	/**
	 * GETTER - SETTER
	 * theInstance
	 */
	inline const InstanceOfBuffer & getInstance() const
	{
		return( mBufferIntance );
	}

	/**
	 * GETTER
	 * mPolicySpecifierKind
	 */
	inline bool hasDeterministicPolicy() const
	{
		return( mBufferIntance.hasDeterministicPolicy() );
	}

	inline bool hasNonDeterministicPolicy() const
	{
		return( mBufferIntance.hasNonDeterministicPolicy() );
	}

};


}

#endif /*BASEBUFFERFORM_H_*/
