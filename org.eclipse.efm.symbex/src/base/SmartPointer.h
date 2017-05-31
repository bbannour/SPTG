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
#ifndef BASE_SMARTPOINTER_H_
#define BASE_SMARTPOINTER_H_

#include <bits/move.h>

#include "SmartPointerUtil.h"

#include <util/avm_numeric.h>


namespace sep
{


template< class T, class Tdestructor >
class SmartPointer
{

private:
	/**
	 * TYPEDEF
	 */
	typedef       SmartPointer< T , Tdestructor >  this_type;

protected:
	/**
	 * TYPEDEF
	 */
	typedef       T   value_type;

	typedef       T & reference;
	typedef const T & const_reference;


	typedef       T * pointer;
	typedef const T * const_pointer;


protected:
	/*
	 * ATTRIBUTES
	 */
	pointer mPTR;


public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	explicit SmartPointer(pointer ptr = NULL)
	: mPTR( ptr )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	SmartPointer(const SmartPointer & other)
	: mPTR( NULL )
	{
		acquire( other.mPTR );
	}

	template< class U >
	SmartPointer(const SmartPointer< U , Tdestructor > & other)
	: mPTR( NULL )
	{
		acquire( other.raw_pointer() );
	}

	/**
	 * DESTRUCTOR
	 */
	~SmartPointer()
	{
		destroy();
	}

	inline void destroy()
	{
		release( NULL );
	}


	/**
	 * REFCOUNT
	 */
	inline avm_uint32_t getRefCount() const
	{
		return( ( mPTR != NULL )? mPTR->getRefCount() : 0 );
	}


	inline bool isUnique() const
	{
		return( (mPTR != NULL)? mPTR->isUnique() : false );
	}

	inline bool isMultiple() const
	{
		return( (mPTR != NULL)? mPTR->isMultiple() : false );
	}


	/**
	 * WRITABILITY
	 */
	inline bool isWritable() const
	{
		return( getRefCount() == 1 );
	}

	inline bool isnotWritable() const
	{
		return( getRefCount() != 1 );
	}

	inline void makeWritable()
	{
//		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
//				<< "raw_pointer in an SmartPointer !!!"
//				<< SEND_EXIT;

		if( mPTR->getRefCount() > 1 )
		{
			mPTR->decrRefCount();

			mPTR = mPTR->clone();
		}
	}


	/**
	 * [IN]VALIDITY
	 */
	inline bool isNull() const
	{
		return( mPTR == NULL );
	}

	inline bool invalid() const
	{
		return( mPTR == NULL );
	}


	inline bool isnotNull() const
	{
		return( mPTR != NULL );
	}

	inline bool valid() const
	{
		return( mPTR != NULL );
	}


	/**
	 * SWAP
	 * FLUSH
	 */
	inline void swap(SmartPointer & other)
	{
		std::swap(mPTR, other.mPTR);
	}

	inline void flush(SmartPointer & other)
	{
		release( other.mPTR );

		other.mPTR = NULL;
	}


	/**
	 * GETTER
	 * mPTR
	 */
	inline pointer raw_pointer() const
	{
		return( mPTR  );
	}

	inline const_reference raw_reference() const
	{
		return( * mPTR  );
	}

	inline avm_address_t raw_address() const
	{
		return( avm_address_t( mPTR ) );
	}


	/**
	 * [RE]SETTER
	 * mPTR
	 */
	inline void acquirePointer(pointer aPtr)
	{
		release_acquire( aPtr );
	}

	inline void setPointer(pointer aPtr)
	{
		release( aPtr );
	}


	inline void replacePointer(pointer aPtr)
	{
		mPTR = aPtr;
	}


	/**
	 * OPERATORS
	 */
//	inline reference operator* () const throw()
//	{
//		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
//				<< "raw_pointer in an SmartPointer !!!"
//				<< SEND_EXIT;
//
//		return( *mPTR );
//	}
//
//	inline pointer operator-> () const
//	{
//		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
//				<< "raw_pointer in an SmartPointer !!!"
//				<< SEND_EXIT;
//
//		return( mPTR );
//    }

	// COMMENT FOR USE IN STL CONTAINER
//	inline pointer operator & () const
//	{
//		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
//				<< "raw_pointer in an SmartPointer !!!"
//				<< SEND_EXIT;
//
//		return( mPTR );
//	}


	/**
	 * CAST
	 */
//	inline operator pointer () const
//	{
//		return( mPTR );
//	}
//
//	// Desactive call of << delete >> using compiler ambiguous mecanism
//	inline operator void * () const
//	{
//		return( mPTR );
//	}


	/**
	 * ASSIGNMENT
	 */
	inline SmartPointer & operator=(pointer aPtr)
	{
		if( mPTR != aPtr )
		{
			release( aPtr );
		}
		return( *this );
	}

	inline SmartPointer & operator=(const SmartPointer & other)
	{
		if( mPTR != other.mPTR )
		{
			release_acquire( other.mPTR );
		}
		return( *this );
	}

	template< class U >
	inline SmartPointer & operator=(
			const SmartPointer< U , Tdestructor > & other)
	{
		if( mPTR != other.raw_pointer() )
		{
			release_acquire( other.raw_pointer() );
		}
		return( *this );
	}


//	template< class U >
//	inline SmartPointer & operator=(U * aPtr)
//	{
//		if( mPTR != aPtr )
//		{
//			release( aPtr );
//		}
//		return( *this );
//	}


	/**
	 * COMPARISON
	 * OPERATOR
	 */

	inline bool operator==(pointer aPtr) const
	{
		return( mPTR == aPtr);
	}

	inline bool operator==(const SmartPointer & other) const
	{
		return( mPTR == other.mPTR );
	}

	template<class U>
	inline bool operator==(
			const SmartPointer< U , Tdestructor > & other) const
	{
		return( mPTR == other.raw_pointer() );
	}


	inline bool operator!=(pointer aPtr) const
	{
		return( mPTR != aPtr );
	}

	inline bool operator!=(const SmartPointer & other) const
	{
		return( mPTR != other.mPTR );
	}

	template<class U>
	inline bool operator!=(
			const SmartPointer< U , Tdestructor > & other) const
	{
		return( mPTR != other.raw_pointer() );
	}


protected:
	/**
	 * acquire
	 * release
	 * release_acquire
	 */
	// increment the count
	inline void acquire(pointer aPtr)
	{
		if( aPtr != NULL )
		{
			aPtr->incrRefCount();
		}
		mPTR = aPtr;
	}


	// decrement the count, delete if it is 0
	inline void release(pointer aPtr)
	{
		Tdestructor::destroy( mPTR );

		mPTR = aPtr;
	}


	inline void release_acquire(pointer aPtr)
	{
		Tdestructor::destroy( mPTR );

		if( aPtr != NULL )
		{
			aPtr->incrRefCount();
		}
		mPTR = aPtr;
	}

};


} /* namespace sep */

#endif /*BASE_SMARTPOINTER_H_*/
