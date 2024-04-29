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
	typedef       T   value_t;

	typedef       T & reference_t;
	typedef const T & const_reference_t;


	typedef       T * pointer_t;
	typedef const T * const_pointer_t;


protected:
	/*
	 * ATTRIBUTES
	 */
	pointer_t mPTR;


public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	explicit SmartPointer(pointer_t ptr = nullptr)
	: mPTR( ptr )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	SmartPointer(const SmartPointer & other)
	: mPTR( nullptr )
	{
		acquire( other.mPTR );
	}

	template< class U >
	SmartPointer(const SmartPointer< U , Tdestructor > & other)
	: mPTR( nullptr )
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
		release( nullptr );
	}


	/**
	 * REFCOUNT
	 */
	inline std::uint32_t getRefCount() const
	{
		return( ( mPTR != nullptr )? mPTR->getRefCount() : 0 );
	}


	inline bool isUnique() const
	{
		return( (mPTR != nullptr)? mPTR->isUnique() : false );
	}

	inline bool isMultiple() const
	{
		return( (mPTR != nullptr)? mPTR->isMultiple() : false );
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
	inline bool isNullptr() const
	{
		return( mPTR == nullptr );
	}

	inline bool invalid() const
	{
		return( mPTR == nullptr );
	}


	inline bool isnotNullptr() const
	{
		return( mPTR != nullptr );
	}

	inline bool valid() const
	{
		return( mPTR != nullptr );
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

		other.mPTR = nullptr;
	}


	/**
	 * GETTER
	 * mPTR
	 */
	inline pointer_t raw_pointer() const
	{
		return( mPTR );
	}

	inline const_reference_t raw_reference() const
	{
		return( * mPTR );
	}

	inline std::intptr_t raw_address() const
	{
		return( std::intptr_t( mPTR ) );
	}


	/**
	 * [RE]SETTER
	 * mPTR
	 */
	inline void acquirePointer(pointer_t aPtr)
	{
		release_acquire( aPtr );
	}

	inline void setPointer(pointer_t aPtr)
	{
		release( aPtr );
	}


	inline void replacePointer(pointer_t aPtr)
	{
		mPTR = aPtr;
	}


	/**
	 * ASSIGNMENT
	 */
	inline SmartPointer & operator=(pointer_t aPtr)
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

	inline bool operator==(pointer_t aPtr) const
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


	inline bool operator!=(pointer_t aPtr) const
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
	inline void acquire(pointer_t aPtr)
	{
		if( aPtr != nullptr )
		{
			aPtr->incrRefCount();
		}
		mPTR = aPtr;
	}


	// decrement the count, delete if it is 0
	inline void release(pointer_t aPtr)
	{
		Tdestructor::destroy( mPTR );

		mPTR = aPtr;
	}


	inline void release_acquire(pointer_t aPtr)
	{
		Tdestructor::destroy( mPTR );

		if( aPtr != nullptr )
		{
			aPtr->incrRefCount();
		}
		mPTR = aPtr;
	}

};

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// Extension for operators:  * ->
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////



template< class T , class Tdestructor >
class XSmartPointer  :  public SmartPointer< T , Tdestructor >
{

private:
	/**
	 * TYPEDEF
	 */
	typedef       SmartPointer < T , Tdestructor >  base_this_type;
	typedef       XSmartPointer< T , Tdestructor >  this_type;

protected:
	typedef       T    value_t;

	typedef       T &  reference_t;
	typedef const T &  const_reference_t;


	typedef       T *  pointer_t;
	typedef const T *  const_pointer_t;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	XSmartPointer()
	: base_this_type( )
	{
		//!!! NOTHING
	}

	explicit XSmartPointer(pointer_t ptr)
	: base_this_type( ptr )
	{
		//!!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	XSmartPointer(const XSmartPointer & other)
	: base_this_type( other )
	{
		//!!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~XSmartPointer()
	{
		//!!! NOTHING
	}


	/**
	 * CAST
	 */
//	inline operator pointer_t () const
//	{
//		return( base_this_type::mPTR );
//	}
//
//	// Desactive call of << delete >> using compiler ambiguous mecanism
//	inline operator void * () const
//	{
//		return( this_type::mPTR );
//	}


	/**
	 * OPERATORS
	 */
//	inline reference_t operator* () const throw()
//	{
//		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
//				<< "raw_pointer in an XSmartPointer !!!"
//				<< SEND_EXIT;
//
//		return( *mPTR );
//	}

	inline pointer_t operator-> () const
	{
		return( base_this_type::mPTR );
	}

	// COMMENT FOR USE IN STL CONTAINER
//	inline pointer_t operator & () const
//	{
//		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
//				<< "raw_pointer in an XSmartPointer !!!"
//				<< SEND_EXIT;
//
//		return( mPTR );
//	}

};



} /* namespace sep */

#endif /*BASE_SMARTPOINTER_H_*/
