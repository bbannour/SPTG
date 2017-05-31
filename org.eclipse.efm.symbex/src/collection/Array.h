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
#ifndef CONTAINER_ARRAY_H_
#define CONTAINER_ARRAY_H_


#include <vector>

#include <util/avm_assert.h>
#include <util/avm_numeric.h>
#include <base/SmartPointerUtil.h>


namespace sep
{


template< typename T >
class Array
{

protected:
	/*
	 * ATTRIBUTES
	 */
	T * mTable;

	avm_size_t mSize;


public:
	/**
	 * TYPEDEF
	 * iterator
	 * reference
	 */
	typedef       T * iterator;
	typedef const T * const_iterator;

	typedef       T & reference;
	typedef const T & const_reference;

	typedef std::vector< T >  BaseVector;



	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Array()
	: mTable( NULL ),
	mSize( 0 )
	{
		//!! NOTHING
	}

	explicit Array(avm_size_t aSize)
	: mTable( NULL ),
	mSize( 0 )
	{
		alloc( aSize );
	}


	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	Array(const Array & anArray)
	: mTable( NULL ),
	mSize( 0 )
	{
		alloc( anArray );
	}


	/**
	 * CONSTRUCTOR
	 * Others
	 */
	explicit Array(avm_size_t aSize, const_reference defaultValue)
	: mTable( NULL ),
	mSize( 0 )
	{
		alloc( aSize , defaultValue );
	}

	explicit Array(const BaseVector & anArray)
	: mTable( NULL ),
	mSize( 0 )
	{
		alloc( anArray );
	}

	explicit Array(const Array & anArray,
			const_reference lastValue)
	: mTable( NULL ),
	mSize( 0 )
	{
		alloc( anArray , lastValue );
	}



	/**
	 * DESTRUCTOR
	 */
	virtual ~Array()
	{
		delete[] ( mTable );

		mTable = NULL;
	}


	/*
	 ***************************************************************************
	 * RESET
	 ***************************************************************************
	 */

	void reset(T value)
	{
		for( avm_size_t offset = 0 ; offset < mSize ; ++offset )
		{
			mTable[offset] = value;
		}
	}


	/*
	 ***************************************************************************
	 * ALLOCATION
	 ***************************************************************************
	 */

	inline void alloc(avm_size_t aSize)
	{
		mSize = aSize;

		mTable = ( (mSize > 0)? (new T[ mSize ]) : NULL );
	}


	inline void alloc(avm_size_t aSize, T defaultValue)
	{
		alloc( aSize );

		for( avm_size_t offset = 0 ; offset < mSize ; ++offset )
		{
			mTable[offset] = defaultValue;
		}
	}


	inline void alloc(const Array & anArray)
	{
		alloc( anArray.size() );

		for( avm_size_t offset = 0 ; offset < mSize ; ++offset )
		{
			mTable[offset] = anArray[offset];
		}
	}


	inline void alloc(const Array & anArray, T lastValue)
	{
		avm_size_t aSize = anArray.size();
		alloc( aSize + 1 );

		for( avm_size_t offset = 0 ; offset < aSize ; ++offset )
		{
			mTable[offset] = anArray[offset];
		}
		mTable[aSize] = lastValue;

	}


	inline void alloc(const BaseVector & anArray)
	{
		alloc( anArray.size() );

		for( avm_size_t offset = 0 ; offset < mSize ; ++offset )
		{
			mTable[offset] = anArray[offset];
		}
	}



	/*
	 ***************************************************************************
	 * RE-ALLOCATION
	 ***************************************************************************
	 */

	inline void realloc(avm_size_t aSize)
	{
		if( mSize != aSize )
		{
			delete[] ( mTable );

			alloc( aSize );
		}
	}


	inline void realloc(avm_size_t aSize, T defaultValue)
	{
		if( mSize != aSize )
		{
			delete[] ( mTable );

			alloc( aSize );
		}

		reset( defaultValue );
	}


	inline void realloc(const Array & anArray)
	{
		if( mSize != anArray.size() )
		{
			delete[] ( mTable );

			alloc( anArray.size() );
		}

		for( avm_size_t offset = 0 ; offset < mSize ; ++offset )
		{
			mTable[offset] = anArray[offset];
		}
	}


	inline void realloc(const BaseVector & anArray)
	{
		if( mSize != anArray.size() )
		{
			delete[] ( mTable );

			alloc( anArray.size() );
		}

		for( avm_size_t offset = 0 ; offset < mSize ; ++offset )
		{
			mTable[offset] = anArray[offset];
		}
	}


	/*
	 ***************************************************************************
	 * RE-SIZE
	 ***************************************************************************
	 */

	inline void resize(avm_size_t aSize)
	{
		if( mSize > 0 )
		{
			avm_size_t oldSize = mSize;
			T * oldTable = mTable;

			alloc( aSize );

			if( aSize > oldSize )
			{
				aSize = oldSize;
			}

			for( avm_size_t offset = 0 ; offset < aSize ; ++offset )
			{
				mTable[offset] = oldTable[offset];
			}

			delete [] oldTable;
		}

		else
		{
			alloc(aSize);
		}
	}

	inline void resize(avm_size_t aSize, T defaultValue)
	{
		if( mSize > 0 )
		{
			avm_size_t oldSize = mSize;
			T * oldTable = mTable;

			alloc( aSize );

			if( aSize > oldSize )
			{
				aSize = oldSize;
			}

			avm_size_t offset = 0;

			for( ; offset < aSize ; ++offset )
			{
				mTable[offset] = oldTable[offset];
			}

			for( ; offset < mSize ; ++offset )
			{
				mTable[offset] = defaultValue;
			}

			delete [] oldTable;
		}

		else
		{
			alloc(aSize, defaultValue);
		}
	}


	/**
	 * ITERATOR
	 */

	inline iterator begin()
	{
		return( mTable );
	}

	inline const_iterator begin() const
	{
		return( mTable );
	}


	inline iterator succ_begin()
	{
		return( (mSize > 0)? mTable +  1 : mTable );
	}

	inline const_iterator succ_begin() const
	{
		return( (mSize > 0)? mTable +  1 : mTable );
	}


	inline iterator end()
	{
		return( mTable + mSize );
	}

	inline const_iterator end() const
	{
		return( mTable + mSize );
	}


	inline iterator pred_end()
	{
		return( (mSize > 0)? mTable + mSize - 1 : mTable );
	}

	inline const_iterator pred_end() const
	{
		return( (mSize > 0)? mTable + mSize - 1 : mTable );
	}



	/**
	 * GETTER - SETTER
	 * mTable
	 */
	inline reference at(avm_size_t offset)
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , mSize ) << SEND_EXIT;

		return( mTable[offset] );
	}

	inline const_reference at(avm_size_t offset) const
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , mSize ) << SEND_EXIT;

		return( mTable[offset] );
	}

	inline reference get(avm_size_t offset)
	{
		return( mTable[offset] );
	}

	inline const_reference get(avm_size_t offset) const
	{
		return( mTable[offset] );
	}


	inline void set(avm_size_t offset, const T & arg)
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , mSize ) << SEND_EXIT;

		mTable[offset] = arg;
	}


	// operator[]
	inline reference operator[](avm_size_t offset)
	{
		return( mTable[offset] );
	}

	inline const_reference operator[](avm_size_t offset) const
	{
		return( mTable[offset] );
	}

	// front() and back()
	inline reference front()
	{
		return mTable[0];
	}

	inline const_reference front() const
	{
		return mTable[0];
	}

	inline reference back()
	{
		return mTable[mSize - 1];
	}

	inline const_reference back() const
	{
		return mTable[mSize - 1];
	}

	// size is constant
	inline avm_size_t size() const
	{
		return( mSize );
	}

	inline bool empty() const
	{
		return( mSize == 0 );
	}

	inline bool nonempty() const
	{
		return( mSize > 0 );
	}

	inline bool singleton() const
	{
		return( mSize == 1 );
	}

	inline bool populated() const
	{
		return( mSize > 1 );
	}


	inline reference first()
	{
		return( mTable[0] );
	}

	inline const_reference first() const
	{
		return( mTable[0] );
	}


	inline reference second()
	{
		return( mTable[1] );
	}

	inline const_reference second() const
	{
		return( mTable[1] );
	}


	inline reference third()
	{
		return( mTable[2] );
	}

	inline const_reference third() const
	{
		return( mTable[2] );
	}


	inline reference last()
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( mSize > 0 )
				<< "last():> Unexpected an empty array !!!"
				<< SEND_EXIT;

		return( mTable[mSize - 1] );
	}

	inline const_reference last() const
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( mSize > 0 )
				<< "last():> Unexpected an empty array !!!"
				<< SEND_EXIT;

		return( mTable[mSize - 1] );
	}

	/**
	 * contains a particular element
	 */
	inline virtual bool contains(const T & arg) const
	{
		const_iterator itEnd = end();
		for( const_iterator it = begin() ; it != itEnd ; ++it )
		{
			if( (*it) == arg )
			{
				return( true );
			}
		}

		return( false );
	}

};


}

#endif /*CONTAINER_ARRAY_H_*/
