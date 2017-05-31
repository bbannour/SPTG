/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 13 janv. 2017
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef BASE_SMARTTABLE_H_
#define BASE_SMARTTABLE_H_

#include <util/avm_assert.h>
#include <util/avm_debug.h>
#include <util/avm_injector.h>
#include <util/avm_numeric.h>

#include <base/ReferenceCounter.h>
#include <base/SmartPointer.h>

#include <printer/OutStream.h>


namespace sep
{

template< class T, class Tdestructor >
class SmartTable
{

protected:
	/**
	 * TYPEDEF
	 */
	typedef       SmartTable  < T , Tdestructor >  this_type;

	typedef       SmartPointer< T , Tdestructor >  smart_pointer_t;

protected:
	/**
	 * TYPEDEF
	 */
	typedef       T   value_type;

	typedef       T & reference_t;
	typedef const T & const_reference_t;

	typedef       T * pointer_t;
	typedef const T * const_pointer_t;

	typedef       T * & reference_pointer_t;
	typedef const T * & const_reference_pointer_t;

	typedef       T * * pointer_pointer_t;
	typedef const T * * const_pointer_pointer_t;

public:
	typedef       T * * iterator;
	typedef T * const * const_iterator;


private:
	/**
	 * Internal Table
	 */
	struct TableT : public ReferenceCounter,
			AVM_INJECT_INSTANCE_COUNTER_CLASS( TableT )
	{

		/**
		 * ATTRIBUTES
		 */
		avm_size_t mSize;

		pointer_pointer_t mElements;
		/**
		 * CONSTRUCTOR
		 * Default
		 */
		TableT()
		: ReferenceCounter( ),
		mSize( 0 ),
		mElements( NULL )
		{
			//!! NOTHING
		}

		TableT(avm_size_t aSize, pointer_t aDefaultValue = NULL)
		: ReferenceCounter( ),
		mSize( aSize ),
		mElements( NULL )
		{
			alloc(aDefaultValue);
		}

		/**
		 * CONSTRUCTOR
		 * Copy
		 */
		TableT(const TableT & aTable)
		: ReferenceCounter( ),
		mSize( aTable.mSize ),
		mElements( NULL )
		{
			acquire( aTable );
		}

		TableT(avm_size_t aSize, const TableT & aTable,
				pointer_t aDefaultValue = NULL)
		: ReferenceCounter( ),
		mSize( aSize ),
		mElements( NULL )
		{
			acquire_resize( aTable, aDefaultValue );
		}

		/**
		 * DESTRUCTOR
		 */
		virtual ~TableT()
		{
			destroyTable();

			mSize = 0;
		}

		inline void destroyTable()
		{
			for( avm_size_t offset = 0 ; offset < mSize ; ++offset )
			{
				Tdestructor::destroy( mElements[ offset ] );
			}
		}

		/**
		 * ALLOCATION
		 */
		inline void alloc(pointer_t aDefaultValue = NULL)
		{
			if( mSize > 0 )
			{
				mElements = new pointer_t[ mSize ];

				for( avm_size_t offset = 0 ; offset < mSize ; ++offset )
				{
					mElements[offset] = aDefaultValue;
				}
			}
			else
			{
				mElements = NULL;
			}
		}

		/**
		 * Resize
		 */
		inline void resize(avm_size_t aSize, pointer_t aDefaultValue = NULL)
		{
			if( aSize == 0 )
			{
				destroyTable();

				mSize = 0;
			}
			else if( mSize > 0 )
			{
				avm_size_t oldSize = mSize;
				pointer_pointer_t oldELements = mElements;

				mElements = new pointer_t[ mSize = aSize ];

				avm_size_t offset = 0;

				// The size increased
				if( aSize >= oldSize )
				{
					for( ; offset < oldSize ; ++offset )
					{
						mElements[offset] = oldELements[offset];
					}
					// Completion
					for( ; offset < aSize ; ++offset )
					{
						mElements[offset] = aDefaultValue;
					}
				}
				// The size decreased
				else
				{
					for( ; offset < aSize ; ++offset )
					{
						mElements[offset] = oldELements[offset];
					}
					// Deletion
					for( ; offset < oldSize ; ++offset )
					{
						Tdestructor::destroy( mElements[ offset ] );
					}
				}

				delete [] oldELements;
			}
			else
			{
				mSize = aSize;

				alloc(aDefaultValue);
			}
		}


		/**
		 * acquire
		 * release
		 * release_acquire
		 */
		inline void acquire(const TableT & aTable)
		{
			if( mSize > 0 )
			{
				mElements = new pointer_t[ mSize ];

				// Acquire
				for( avm_size_t offset = 0 ; offset < mSize ; ++offset )
				{
					acquire(offset, aTable.mElements[offset]);
				}
			}
			else
			{
				mElements = NULL;
			}
		}

		inline void acquire_resize(
				const TableT & aTable, pointer_t aDefaultValue)
		{
			if( mSize > 0 )
			{
				mElements = new pointer_t[ mSize ];

				avm_size_t offset = 0;

				avm_size_t minBound = std::min(mSize, aTable.mSize);

				// Acquire
				for( ; offset < minBound ; ++offset )
				{
					acquire(offset, aTable.mElements[offset]);
				}
				// Completion if need
				for( ; offset < mSize ; ++offset )
				{
					mElements[offset] = aDefaultValue;
				}
			}
			else
			{
				mElements = NULL;
			}
		}


		inline void acquire(avm_size_t offset, pointer_t anElement)
		{
			if( anElement != NULL )
			{
				anElement->incrRefCount();
			}

			mElements[offset] = anElement;
		}

		inline void release(avm_size_t offset, pointer_t anElement)
		{
			Tdestructor::destroy( mElements[offset] );

			mElements[offset] = anElement;
		}

		inline void release_acquire(avm_size_t offset, pointer_t anElement)
		{
			Tdestructor::destroy( mElements[offset] );

			if( anElement != NULL )
			{
				anElement->incrRefCount();
			}

			mElements[offset] = anElement;
		}


		/**
		 * Writable
		 */
		inline TableT * clone_acquire() const
		{
			return( new TableT(*this) );
		}

		inline TableT * clone_resize_acquire(
				avm_size_t aSize, pointer_t aDefaultValue = NULL) const
		{
			return( new TableT(aSize, *this, aDefaultValue) );
		}

	};

protected:
	/**
	 * TYPEDEF
	 */
	typedef TableT   table_type;
	typedef TableT * table_pointer_t;


protected:
	/*
	 * ATTRIBUTES
	 */
	table_pointer_t mTable;


public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	explicit SmartTable(table_pointer_t aTable = NULL)
	: mTable( aTable )
	{
		//!! NOTHING
	}

	SmartTable(avm_size_t aSize, pointer_t aDefaultValue = NULL)
	: mTable( new table_type(aSize, aDefaultValue) )
	{
		//!! NOTHING
	}

	SmartTable(avm_size_t aSize,
			const SmartTable & aSmartTable, pointer_t aDefaultValue = NULL)
	: mTable( NULL )
	{
		if( aSize == aSmartTable.size() )
		{
			acquire( aSmartTable.mTable );
		}
		else
		{
			mTable = aSmartTable.mTable
					->clone_resize_acquire(aSize, aDefaultValue);
		}
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	SmartTable(const SmartTable & aSmartTable)
	: mTable( NULL )
	{
		acquire( aSmartTable.mTable );
	}

	template< class U >
	SmartTable(const SmartTable< U , Tdestructor > & aSmartTable)
	: mTable( NULL )
	{
		acquire( aSmartTable.mTable );
	}

	/**
	 * DESTRUCTOR
	 */
	~SmartTable()
	{
		destroy();
	}

	inline void destroy()
	{
		destroyTable( mTable );
	}

	inline void destroyTable(table_pointer_t & aTable)
	{
		if( aTable != NULL )
		{
			if( aTable->isUnique() )
			{
				delete( aTable );
			}
			else
			{
				aTable->decrRefCount();
			}

			aTable = NULL;
		}
	}


	/**
	 * mSize
	 */
	inline avm_size_t size() const
	{
		return( (mTable == NULL) ? 0 : mTable->mSize );
	}

	inline bool empty() const
	{
		return( (mTable == NULL) || (mTable->mSize == 0) );
	}

	inline bool nonempty() const
	{
		return( (mTable != NULL) && (mTable->mSize > 0) );
	}

	inline bool populated() const
	{
		return( (mTable != NULL) && (mTable->mSize > 1) );
	}


	/**
	 * GETTER
	 * for element at given position by reference
	 * return( [const_]pointer_t )
	 */
	inline pointer_t at(avm_size_t offset)
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , size() )
				<< SEND_EXIT;

		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mTable->mElements[offset] )
				<< " pointer in an SmartTable at offset: " << offset << " !!!"
				<< SEND_EXIT;

		return( mTable->mElements[offset] );
	}

	inline const_pointer_t at(avm_size_t offset) const
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , size() )
				<< SEND_EXIT;

		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mTable->mElements[offset] )
				<< " pointer in an SmartTable at offset: " << offset << " !!!"
				<< SEND_EXIT;

		return( mTable->mElements[offset] );
	}

	/**
	 * GETTER
	 * for element at given position
	 * return( [const_]reference_t )
	 */
	inline reference_t ref(avm_size_t offset)
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , size() )
				<< SEND_EXIT;

		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mTable->mElements[offset] )
				<< " pointer in an SmartTable at offset: " << offset << " !!!"
				<< SEND_EXIT;

		return( *( mTable->mElements[offset] ) );
	}

	inline const_reference_t ref(avm_size_t offset) const
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , size() )
				<< SEND_EXIT;

		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mTable->mElements[offset] )
				<< " pointer in an SmartTable at offset: " << offset << " !!!"
				<< SEND_EXIT;

		return( *( mTable->mElements[offset] ) );
	}


	/**
	 * SETTER
	 * for element at given position
	 */
	inline void set(avm_size_t offset, pointer_t anElement) const
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , size() )
				<< SEND_EXIT;

		mTable->mElements[offset] = anElement;
	}

	inline void append(pointer_t anElement) const
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( 0 , size() )
				<< SEND_EXIT;

		avm_size_t offset = 0;
		for( ; offset < mTable->mSize ; ++offset )
		{
			if( mTable->mElements[ offset ] == NULL )
			{
				mTable->mElements[offset] = anElement;

				return;
			}
		}

		AVM_OS_ASSERT_FATAL_ERROR_EXIT( offset < mTable->mSize )
				<< "Unexpected a full SmartTable in method append(...) !"
				<< SEND_EXIT;
	}

	/**
	 * SETTER
	 * for element at given position
	 * update reference counter:> release acquire
	 */
	inline void assign(avm_size_t offset, pointer_t anElement) const
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , size() )
				<< SEND_EXIT;

		mTable->release_acquire(offset, anElement);
	}

	inline void assign(avm_size_t offset,
			const smart_pointer_t & anElement) const
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , size() )
				<< SEND_EXIT;

		mTable->release_acquire(offset, anElement.raw_pointer());
	}

	/**
	 * GETTER
	 * for element at given position
	 * return( Smart Pointer )
	 */
	template< class SmartPointerT >
	inline SmartPointerT to_sp(avm_size_t offset) const
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , size() )
				<< SEND_EXIT;

		if( //(mTable != NULL) && (mTable->mSize > offset) &&
			(mTable->mElements[ offset ] != NULL) )
		{
			mTable->mElements[ offset ]->incrRefCount();

			return( SmartPointerT( mTable->mElements[offset] ) );
		}

		return( SmartPointerT() );
	}


	/**
	 * GETTER
	 * for element at given position
	 * operator[]
	 * return( [const_]reference_t )
	 */
	inline reference_t operator[](avm_size_t offset)
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , size() )
				<< SEND_EXIT;

		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mTable->mElements[offset] )
				<< " pointer in an SmartTable at offset: " << offset << " !!!"
				<< SEND_EXIT;

		return( *( mTable->mElements[offset] ) );
	}

	inline const_reference_t operator[](avm_size_t offset) const
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , size() )
				<< SEND_EXIT;

		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mTable->mElements[offset] )
				<< " pointer in an SmartTable at offset: " << offset << " !!!"
				<< SEND_EXIT;

		return( *( mTable->mElements[offset] ) );
	}

	/**
	 * GETTER
	 * for element at ( front | back ) position
	 * return( [const_]pointer_t )
	 */
	inline reference_pointer_t front()
	{
		return((size() == 0) ? NULL : mTable->mElements[ 0 ] );
	}

	inline const_reference_pointer_t front() const
	{
		return( (size() == 0) ? NULL : mTable->mElements[ 0 ] );
	}

	inline reference_pointer_t back()
	{
		return( (size() == 0) ? NULL : mTable->mElements[mTable->mSize - 1] );
	}

	inline const_reference_pointer_t back() const
	{
		return( (size() == 0) ? NULL : mTable->mElements[mTable->mSize - 1] );
	}


	/**
	 * ITERATOR
	 */
	inline iterator begin()
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mTable )
				<< " Table in an SmartTable !!!"
				<< SEND_EXIT;

		return( mTable->mElements );
	}

	inline const_iterator begin() const
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mTable )
				<< " Table in an SmartTable !!!"
				<< SEND_EXIT;

		return( mTable->mElements );
	}


	inline iterator end()
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mTable )
				<< " Table in an SmartTable !!!"
				<< SEND_EXIT;

		return( mTable->mElements + size() );
	}

	inline const_iterator end() const
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mTable )
				<< " Table in an SmartTable !!!"
				<< SEND_EXIT;

		return( mTable->mElements + size() );
	}


	/**
	 * REFCOUNT
	 */
	inline avm_uint32_t getRefCount() const
	{
		return( ( mTable == NULL ) ? 0 : mTable->getRefCount() );
	}


	inline bool isUnique() const
	{
		return( (mTable == NULL) ? false : mTable->isUnique() );
	}

	inline bool isMultiple() const
	{
		return( (mTable == NULL) ? false : mTable->isMultiple() );
	}

	/**
	 * AVM DEBUG REF COUNTER
	 */
	inline void AVM_DEBUG_REF_COUNTER(OutStream & os) const
	{
AVM_IF_DEBUG_FLAG( REFERENCE_COUNTING )
		if( mTable != NULL )
		{
			os << " /* < ref: " << mTable->getRefCount() << " > */";
		}
		else
		{
			os << " /* < ref: SmartTable<null> */";
		}
		os << std::flush;
AVM_ENDIF_DEBUG_FLAG( REFERENCE_COUNTING )
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
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mTable )
				<< " Table in an SmartTable !!!"
				<< SEND_EXIT;

		if( mTable->isMultiple() )
		{
			mTable->decrRefCount();

			mTable = mTable->clone_acquire();
		}
	}

	inline void makeWritable(avm_size_t offset)
	{
		makeWritable();

		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mTable->mElements[offset] )
				<< " pointer in an SmartTable at offset: " << offset << " !!!"
				<< SEND_EXIT;

		if( mTable->mElements[offset]->isMultiple() )
		{
			mTable->mElements[offset]->decrRefCount();

			mTable->mElements[offset] = mTable->mElements[offset]->clone();
		}
	}

	/**
	 * GETTER
	 * for witable element at given position
	 * return( reference_pointer_t )
	 */
	inline reference_pointer_t getWritable(avm_size_t offset)
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , size() )
				<< SEND_EXIT;

		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mTable->mElements[offset] )
				<< " pointer in an SmartTable at offset: " << offset << " !!!"
				<< SEND_EXIT;

		makeWritable();

		if( mTable->mElements[offset]->isMultiple() )
		{
			mTable->mElements[offset]->decrRefCount();

			mTable->mElements[offset] = mTable->mElements[offset]->clone();
		}

		return( mTable->mElements[offset] );
	}

	/**
	 * GETTER
	 * for witable element at given position
	 * return( reference_t )
	 */
	inline reference_t refWritable(avm_size_t offset)
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , size() )
				<< SEND_EXIT;

		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mTable->mElements[offset] )
				<< " pointer in an SmartTable at offset: " << offset << " !!!"
				<< SEND_EXIT;

		makeWritable();

		if( mTable->mElements[offset]->isMultiple() )
		{
			mTable->mElements[offset]->decrRefCount();

			mTable->mElements[offset] = mTable->mElements[offset]->clone();
		}

		return( *( mTable->mElements[offset] ) );
	}

//	template< class ElementT >
//	inline reference_pointer_t getWritable(ElementT * anElement)
//	{
//		return( getWritable( anElement->getOffset() ) );
//	}

	/**
	 * GETTER
	 * for witable element at given position
	 * return( SmartPointerT )
	 */
	template< class SmartPointerT >
	inline SmartPointerT spWritable(avm_size_t offset)
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , size() )
				<< SEND_EXIT;

		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mTable->mElements[offset] )
				<< " pointer in an SmartTable at offset: " << offset << " !!!"
				<< SEND_EXIT;

		makeWritable();

		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mTable->mElements[offset] )
				<< " pointer in an SmartTable at offset: " << offset << " !!!"
				<< SEND_EXIT;

		if( mTable->mElements[offset]->isMultiple() )
		{
			mTable->mElements[offset]->decrRefCount();

			mTable->mElements[offset] = mTable->mElements[offset]->clone();
		}

		mTable->mElements[ offset ]->incrRefCount();

		return( SmartPointerT(mTable->mElements[offset]) );
	}


	/**
	 * RESIZE
	 */
	inline void makeWritableResize(
			avm_size_t aSize, pointer_t aDefaultValue = NULL)
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mTable )
				<< " Table in an SmartTable !!!"
				<< SEND_EXIT;

		if( mTable->isMultiple() )
		{
			mTable->decrRefCount();

			mTable = mTable->clone_resize_acquire(aSize, aDefaultValue);
		}
		else // if( mTable->isUnique() > 1 )
		{
			mTable->resize(aSize, aDefaultValue);
		}
	}

	/**
	 * [IN]VALIDITY
	 */
	inline bool isNull() const
	{
		return( mTable == NULL );
	}

	inline bool isNull(avm_size_t offset) const
	{
//		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mTable )
//				<< " Table in an SmartTable !!!"
//				<< SEND_EXIT;

		return( (mTable == NULL)
				|| (mTable->mElements[offset] == NULL) );
	}

	inline bool invalid() const
	{
		return( mTable == NULL );
	}

	inline bool invalid(avm_size_t offset) const
	{
//		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mTable )
//				<< " Table in an SmartTable !!!"
//				<< SEND_EXIT;

		return( (mTable == NULL)
				|| (mTable->mElements[offset] == NULL) );
	}


	inline bool isnotNull() const
	{
		return( mTable != NULL );
	}

	inline bool isnotNull(avm_size_t offset) const
	{
//		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mTable )
//				<< " Table in an SmartTable !!!"
//				<< SEND_EXIT;

		return( (mTable != NULL)
				&& (mTable->mElements[offset] != NULL) );
	}


	inline bool valid() const
	{
		return( mTable != NULL );
	}

	inline bool valid(avm_size_t offset) const
	{
//		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mTable )
//				<< " Table in an SmartTable !!!"
//				<< SEND_EXIT;

		return( (mTable != NULL)
				&& (mTable->mElements[offset] != NULL) );
	}


	/**
	 * SWAP
	 * FLUSH
	 */
	inline void swap(SmartTable & other)
	{
		std::swap(mTable, other.mTable);
	}

	inline void flush(SmartTable & other)
	{
		release( other.mTable );

		other.mTable = NULL;
	}


	/**
	 * GETTER
	 * mTable
	 */
	inline avm_address_t raw_address() const
	{
		return( avm_address_t( mTable ) );
	}

	/**
	 * ASSIGNMENT
	 */
	inline SmartTable & operator=(table_pointer_t aTable)
	{
		if( mTable != aTable )
		{
			release( aTable );
		}
		return( *this );
	}

	inline SmartTable & operator=(const SmartTable & other)
	{
		if( mTable != other.mTable )
		{
			release_acquire( other.mTable );
		}
		return( *this );
	}


	/**
	 * COMPARISON
	 * OPERATOR
	 */

	inline bool operator==(table_pointer_t aTable) const
	{
		return( mTable == aTable );
	}

	inline bool operator==(const SmartTable & other) const
	{
		return( mTable == other.mTable );
	}

	template<class U>
	inline bool operator==(
			const SmartTable< U , Tdestructor > & other) const
	{
		return( mTable == other.raw_pointer() );
	}


	inline bool operator!=(table_pointer_t aTable) const
	{
		return( mTable != aTable );
	}

	inline bool operator!=(const SmartTable & other) const
	{
		return( mTable != other.mTable );
	}

	template<class U>
	inline bool operator!=(
			const SmartTable< U , Tdestructor > & other) const
	{
		return( mTable != other.raw_pointer() );
	}


protected:
	/**
	 * acquire
	 * release
	 * release_acquire
	 */
	// increment the count
	inline void acquire(table_pointer_t aTable)
	{
		if( aTable != NULL )
		{
			aTable->incrRefCount();
		}

		mTable = aTable;
	}


	// decrement the count, delete if it is 0
	inline void release(table_pointer_t aTable)
	{
		destroyTable( mTable );

		mTable = aTable;
	}


	inline void release_acquire(table_pointer_t aTable)
	{
		destroyTable( mTable );

		if( aTable != NULL )
		{
			aTable->incrRefCount();
		}

		mTable = aTable;
	}


public:
	/**
	 * Serialization
	 */
	inline std::string str() const
	{
		std::ostringstream oss;

		if( mTable != NULL )
		{
			if( mTable->mSize > 0 )
			{
				oss << "[ " << mTable->mElements[ 0 ]->str();

				for( avm_size_t offset = 1 ; offset < mTable->mSize ; ++offset )
				{
					if( mTable->mElements[ offset ] != NULL )
					{
						oss	<< " , " << mTable->mElements[ offset ]->str();
					}
					else
					{
						oss << " , null< T * >";
					}
				}

				oss << " ]";

				return( oss.str() );
			}
			else
			{
				return( "empty<SmartTable>" );
			}
		}
		else
		{
			return( "null<SmartTable>" );
		}
	}

	inline std::string toString(
			const AvmIndent & indent = AVM_TAB_INDENT) const
	{
		StringOutStream oss(indent);

		toStream( oss );

		return( oss.str() );
	}

	inline void toStream(OutStream & os) const
	{
		if( mTable != NULL )
		{
			if( mTable->mSize > 0 )
			{
				for( avm_size_t offset = 0 ; offset < mTable->mSize ; ++offset )
				{
					if( mTable->mElements[ offset ] != NULL )
					{
						mTable->mElements[ offset ]->toStream(os);
					}
					else
					{
						os << TAB << "null< T * >" << EOL;
					}
					os << std::flush;
				}
			}
			else
			{
				os << TAB << "empty<SmartTable>" << EOL_FLUSH;
			}
		}
		else
		{
			os << TAB << "null<SmartTable>" << EOL_FLUSH;
		}
	}

};


} /* namespace sep */

#endif /* BASE_SMARTTABLE_H_ */
