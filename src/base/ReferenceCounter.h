/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 19 mars 2016
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef BASE_REFERENCECOUNTER_H_
#define BASE_REFERENCECOUNTER_H_

#include <printer/OutStream.h>			// printer/OutStream.h
#include <util/avm_debug.h>		// util/avm_debug.h
#include <util/avm_numeric.h>	// util/avm_debug.h


namespace sep
{

class ReferenceCounter
{

protected:
	/**
	 * ATTRIBUTE
	 */
	std::uint32_t mReferenceCount;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ReferenceCounter( std::uint32_t count = 1 )
	: mReferenceCount( count )
	{
			//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~ReferenceCounter()
	{
		mReferenceCount = 0;
	}


	/**
	 * AVM DEBUG REF COUNTER
	 */
	inline void AVM_DEBUG_REF_COUNTER(OutStream & os) const
	{
AVM_IF_DEBUG_FLAG( REFERENCE_COUNTING )
		os << " /* < ref: " << getRefCount() << " > */" << std::flush;
AVM_ENDIF_DEBUG_FLAG( REFERENCE_COUNTING )
	}

	inline std::string AVM_DEBUG_REF_COUNTER() const
	{
		StringOutStream oss;

		AVM_DEBUG_REF_COUNTER(oss);

		return( oss.str() );
	}

	inline std::string strRefCount() const
	{
		return( OSS() << " /* < ref: " << getRefCount() << " > */" );
	}


	/**
	 * GETTER - SETTER
	 * mReferenceCount
	 */
	inline std::uint32_t getRefCount() const
	{
		return( mReferenceCount );
	}

	inline void setRefCount(std::uint32_t count)
	{
		mReferenceCount = count;
	}


	/**
	 * REFERCENCE COUNT
	 * MANAGEMENT
	 */
	inline void decrRefCount()
	{
		--mReferenceCount;
	}

	inline void incrRefCount()
	{
		++mReferenceCount;
	}


	/**
	 * LIFECYCLE
	 */
	inline bool isAlive() const
	{
		return( mReferenceCount > 0 );
	}

	inline bool isDead() const
	{
		return( mReferenceCount == 0 );
	}

	/**
	 * MULTIPLICITY
	 */
	inline bool isUnique() const
	{
		return( mReferenceCount == 1 );
	}

	inline bool isMultiple() const
	{
		return( mReferenceCount >= 2 );
	}


	/**
	 * WRITABILITY
	 */
	inline bool isWritable() const
	{
		return( mReferenceCount == 1 );
	}

	inline bool isnotWritable() const
	{
		return( mReferenceCount != 1 );
	}

};


/**
 * MEMORY MANAGEMENT
 * INCR - DECR
 * REFCOUNT
 */

template< class T >
T * incrReferenceCount(T * anElement)
{
	if( anElement != nullptr )
	{
		anElement->incrRefCount();
	}

	return( anElement );
}



} /* namespace sep */

#endif /* BASE_REFERENCECOUNTER_H_ */
