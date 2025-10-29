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
#include <util/avm_numeric.h>

#include <base/Injector.h>
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
	struct TableT final : public ReferenceCounter,
			AVM_INJECT_INSTANCE_COUNTER_CLASS( TableT )
	{

		/**
		 * ATTRIBUTES
		 */
		std::size_t mSize;

		pointer_pointer_t mElements;
		/**
		 * CONSTRUCTOR
		 * Default
		 */
		TableT()
		: ReferenceCounter( ),
		mSize( 0 ),
		mElements( nullptr )
		{
			//!! NOTHING
		}

		TableT(std::size_t aSize, pointer_t aDefaultValue = nullptr)
		: ReferenceCounter( ),
		mSize( aSize ),
		mElements( nullptr )
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
		mElements( nullptr )
		{
			acquire( aTable );
		}

		TableT(std::size_t aSize, const TableT & aTable,
				pointer_t aDefaultValue = nullptr)
		: ReferenceCounter( ),
		mSize( aSize ),
		mElements( nullptr )
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
			for( std::size_t offset = 0 ; offset < mSize ; ++offset )
			{
				Tdestructor::destroy( mElements[ offset ] );
			}
		}

		/**
		 * ALLOCATION
		 */
		inline void alloc(pointer_t aDefaultValue = nullptr)
		{
			if( mSize > 0 )
			{
				mElements = new pointer_t[ mSize ];

				for( std::size_t offset = 0 ; offset < mSize ; ++offset )
				{
					mElements[offset] = aDefaultValue;
				}
			}
			else
			{
				mElements = nullptr;
			}
		}

		/**
		 * Resize
		 */
		inline void resize(std::size_t aSize, pointer_t aDefaultValue = nullptr)
		{
			if( aSize == 0 )
			{
				destroyTable();

				mSize = 0;
			}
			else if( mSize > 0 )
			{
				std::size_t oldSize = mSize;
				pointer_pointer_t oldELements = mElements;

				mElements = new pointer_t[ mSize = aSize ];

				std::size_t offset = 0;

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
				for( std::size_t offset = 0 ; offset < mSize ; ++offset )
				{
					acquire(offset, aTable.mElements[offset]);
				}
			}
			else
			{
				mElements = nullptr;
			}
		}

		inline void acquire_resize(
				const TableT & aTable, pointer_t aDefaultValue)
		{
			if( mSize > 0 )
			{
				mElements = new pointer_t[ mSize ];

				std::size_t offset = 0;

				std::size_t minBound = std::min(mSize, aTable.mSize);

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
				mElements = nullptr;
			}
		}


		inline void acquire(std::size_t offset, pointer_t anElement)
		{
			if( anElement != nullptr )
			{
				anElement->incrRefCount();
			}

			mElements[offset] = anElement;
		}

		inline void release(std::size_t offset, pointer_t anElement)
		{
			Tdestructor::destroy( mElements[offset] );

			mElements[offset] = anElement;
		}

		inline void release_acquire(std::size_t offset, pointer_t anElement)
		{
			Tdestructor::destroy( mElements[offset] );

			if( anElement != nullptr )
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
				std::size_t aSize, pointer_t aDefaultValue = nullptr) const
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
	explicit SmartTable(table_pointer_t aTable = nullptr)
	: mTable( aTable )
	{
		//!! NOTHING
	}

	SmartTable(std::size_t aSize, pointer_t aDefaultValue = nullptr)
	: mTable( new table_type(aSize, aDefaultValue) )
	{
		//!! NOTHING
	}

	SmartTable(std::size_t aSize,
			const SmartTable & aSmartTable, pointer_t aDefaultValue = nullptr)
	: mTable( nullptr )
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
	: mTable( nullptr )
	{
		acquire( aSmartTable.mTable );
	}

	template< class U >
	SmartTable(const SmartTable< U , Tdestructor > & aSmartTable)
	: mTable( nullptr )
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
		if( aTable != nullptr )
		{
			if( aTable->isUnique() )
			{
				delete( aTable );
			}
			else
			{
				aTable->decrRefCount();
			}

			aTable = nullptr;
		}
	}


	/**
	 * mSize
	 */
	inline std::size_t size() const
	{
		return( (mTable == nullptr) ? 0 : mTable->mSize );
	}

	inline bool empty() const
	{
		return( (mTable == nullptr) || (mTable->mSize == 0) );
	}

	inline bool nonempty() const
	{
		return( (mTable != nullptr) && (mTable->mSize > 0) );
	}

	inline bool populated() const
	{
		return( (mTable != nullptr) && (mTable->mSize > 1) );
	}


	/**
	 * GETTER
	 * for element at given position by reference
	 * return( [const_]pointer_t )
	 */
	inline pointer_t at(std::size_t offset)
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , size() )
				<< SEND_EXIT;

		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mTable->mElements[offset] )
				<< " pointer in an SmartTable at offset: " << offset << " !!!"
				<< SEND_EXIT;

		return( mTable->mElements[offset] );
	}

	inline const_pointer_t at(std::size_t offset) const
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
	inline reference_t ref(std::size_t offset)
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , size() )
				<< SEND_EXIT;

		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mTable->mElements[offset] )
				<< " pointer in an SmartTable at offset: " << offset << " !!!"
				<< SEND_EXIT;

		return( *( mTable->mElements[offset] ) );
	}

	inline const_reference_t ref(std::size_t offset) const
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
	inline void set(std::size_t offset, pointer_t anElement) const
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , size() )
				<< SEND_EXIT;

		mTable->mElements[offset] = anElement;
	}

	inline void append(pointer_t anElement) const
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( 0 , size() )
				<< SEND_EXIT;

		std::size_t offset = 0;
		for( ; offset < mTable->mSize ; ++offset )
		{
			if( mTable->mElements[ offset ] == nullptr )
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
	inline void assign(std::size_t offset, pointer_t anElement) const
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , size() )
				<< SEND_EXIT;

		mTable->release_acquire(offset, anElement);
	}

	inline void assign(std::size_t offset,
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
	inline SmartPointerT to_sp(std::size_t offset) const
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , size() )
				<< SEND_EXIT;

		if( //(mTable != nullptr) && (mTable->mSize > offset) &&
			(mTable->mElements[ offset ] != nullptr) )
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
	inline reference_t operator[](std::size_t offset)
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , size() )
				<< SEND_EXIT;

		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mTable->mElements[offset] )
				<< " pointer in an SmartTable at offset: " << offset << " !!!"
				<< SEND_EXIT;

		return( *( mTable->mElements[offset] ) );
	}

	inline const_reference_t operator[](std::size_t offset) const
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
		return((size() == 0) ? nullptr : mTable->mElements[ 0 ] );
	}

	inline const_reference_pointer_t front() const
	{
		return( (size() == 0) ? nullptr : mTable->mElements[ 0 ] );
	}

	inline reference_pointer_t back()
	{
		return( (size() == 0) ? nullptr : mTable->mElements[mTable->mSize - 1] );
	}

	inline const_reference_pointer_t back() const
	{
		return( (size() == 0) ? nullptr : mTable->mElements[mTable->mSize - 1] );
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
	inline std::uint32_t getRefCount() const
	{
		return( ( mTable == nullptr ) ? 0 : mTable->getRefCount() );
	}


	inline bool isUnique() const
	{
		return( (mTable == nullptr) ? false : mTable->isUnique() );
	}

	inline bool isMultiple() const
	{
		return( (mTable == nullptr) ? false : mTable->isMultiple() );
	}

	/**
	 * AVM DEBUG REF COUNTER
	 */
	inline void AVM_DEBUG_REF_COUNTER(OutStream & os) const
	{
AVM_IF_DEBUG_FLAG( REFERENCE_COUNTING )
		if( mTable != nullptr )
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

	inline void makeWritable(std::size_t offset)
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
	inline reference_pointer_t getWritable(std::size_t offset)
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
	inline reference_t refWritable(std::size_t offset)
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
	inline SmartPointerT spWritable(std::size_t offset)
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
			std::size_t aSize, pointer_t aDefaultValue = nullptr)
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
	inline bool isNullptr() const
	{
		return( mTable == nullptr );
	}

	inline bool isNullptr(std::size_t offset) const
	{
//		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mTable )
//				<< " Table in an SmartTable !!!"
//				<< SEND_EXIT;

		return( (mTable == nullptr)
				|| (mTable->mElements[offset] == nullptr) );
	}

	inline bool invalid() const
	{
		return( mTable == nullptr );
	}

	inline bool invalid(std::size_t offset) const
	{
//		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mTable )
//				<< " Table in an SmartTable !!!"
//				<< SEND_EXIT;

		return( (mTable == nullptr)
				|| (mTable->mElements[offset] == nullptr) );
	}


	inline bool isnotNullptr() const
	{
		return( mTable != nullptr );
	}

	inline bool isnotNullptr(std::size_t offset) const
	{
//		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mTable )
//				<< " Table in an SmartTable !!!"
//				<< SEND_EXIT;

		return( (mTable != nullptr)
				&& (mTable->mElements[offset] != nullptr) );
	}


	inline bool valid() const
	{
		return( mTable != nullptr );
	}

	inline bool valid(std::size_t offset) const
	{
//		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mTable )
//				<< " Table in an SmartTable !!!"
//				<< SEND_EXIT;

		return( (mTable != nullptr)
				&& (mTable->mElements[offset] != nullptr) );
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

		other.mTable = nullptr;
	}


	/**
	 * GETTER
	 * mTable
	 */
	inline std::intptr_t raw_address() const
	{
		return( std::intptr_t( mTable ) );
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
		if( aTable != nullptr )
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

		if( aTable != nullptr )
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

		if( mTable != nullptr )
		{
			if( mTable->mSize > 0 )
			{
				oss << "[ " << mTable->mElements[ 0 ]->str();

				for( std::size_t offset = 1 ; offset < mTable->mSize ; ++offset )
				{
					if( mTable->mElements[ offset ] != nullptr )
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
		if( mTable != nullptr )
		{
			if( mTable->mSize > 0 )
			{
				for( std::size_t offset = 0 ; offset < mTable->mSize ; ++offset )
				{
					if( mTable->mElements[ offset ] != nullptr )
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
