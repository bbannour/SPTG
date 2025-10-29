/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 8 févr. 2010
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef BUILTINARRAY_H_
#define BUILTINARRAY_H_

#include <fml/expression/BuiltinContainer.h>

#include <collection/Pair.h>

#include <common/BF.h>

#include <fml/type/BaseTypeSpecifier.h>


namespace sep
{


class ArrayBF;
class AvmInstruction;


class BuiltinArray :
		public BuiltinCollection ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( BuiltinArray )
{

protected:
	/**
	 * ATTRIBUTES
	 */
	const BaseTypeSpecifier * mTypeSpecifier;

	std::size_t mSize;


public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BuiltinArray(class_kind_t aTypeId,
			const BaseTypeSpecifier & aTypeSpecifier, std::size_t aSize = 0)
	: BuiltinCollection( aTypeId ),
	mTypeSpecifier( & aTypeSpecifier ),
	mSize( aSize )
	{
		//!!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	BuiltinArray(const BuiltinArray & anArray)
	: BuiltinCollection( anArray ),
	mTypeSpecifier( anArray.mTypeSpecifier ),
	mSize( anArray.mSize )
	{
		//!!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~BuiltinArray()
	{
		mSize = 0;
	}


	/**
	 * GETTER - SETTER
	 * mTypeSpecifier
	 */
	inline const BaseTypeSpecifier & getTypeSpecifier() const
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mTypeSpecifier )
				<< "TypeSpecifier for " << toString() << "!!!"
				<< SEND_EXIT;

		return( * mTypeSpecifier );
	}

	inline avm_type_specifier_kind_t getTypeSpecifierKind() const
	{
		return( (mTypeSpecifier != nullptr) ?
				mTypeSpecifier->getTypeSpecifierKind() : TYPE_NULL_SPECIFIER );
	}

	inline bool hasTypeSpecifier() const
	{
		return( mTypeSpecifier != nullptr );
	}

//!@?MISUSED: TO DELETE
	inline void setTypeSpecifier(const BaseTypeSpecifier & aTypeSpecifier)
	{
		mTypeSpecifier = (& aTypeSpecifier);
	}


	// size is constant
	inline std::size_t size() const override final
	{
		return( mSize );
	}

	inline std::size_t capacity() const override
	{
		return( mSize );
	}

	inline void setCapacity(long aCapacity) override
	{
		AVM_OS_FATAL_ERROR_EXIT << "NO SENSE HERE !!!" << SEND_EXIT;
	}


	inline bool empty() const override
	{
		return( mSize == 0 );
	}

	inline bool nonempty() const override
	{
		return( mSize > 0 );
	}

	inline bool singleton() const override
	{
		return( mSize == 1 );
	}

	inline bool populated() const override
	{
		return( mSize > 1 );
	}



	inline virtual bool contains(const BF & arg) const override
	{
		return( false );
	}


	// CAST
	virtual ArrayBF * getArrayBF() const = 0;


	static class_kind_t getArrayTypeId(class_kind_t aTypeId);

	static class_kind_t getArrayTypeId(
			class_kind_t classKindA, class_kind_t classKindB);

	static BF create(const BFVector & array);


	/**
	 * Serialization
	 */
	using BuiltinCollection::str;

	virtual std::string str(std::size_t offset) const = 0;

};



template< typename T >
class _BuiltinArray_  :  public BuiltinArray
{

protected:
	/**
	 * ATTRIBUTES
	 */

	T * mTable;


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

	typedef std::vector< T > BaseVector;


	/**
	 * CONSTRUCTOR
	 * Default
	 */
	_BuiltinArray_(class_kind_t aTypeId,
			const BaseTypeSpecifier & aTypeSpecifier, std::size_t aSize = 0)
	: BuiltinArray( aTypeId , aTypeSpecifier, aSize ),
	mTable( nullptr )
	{
		alloc( aSize );
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	_BuiltinArray_(const _BuiltinArray_ & anArray)
	: BuiltinArray( anArray ),
	mTable( nullptr )
	{
		alloc( anArray );
	}


	/**
	 * CONSTRUCTOR
	 * Other
	 */
	_BuiltinArray_(class_kind_t aTypeId,
			const BaseTypeSpecifier & aTypeSpecifier,
			std::size_t aSize, T defaultValue)
	: BuiltinArray( aTypeId , aTypeSpecifier , aSize ),
	mTable( nullptr )
	{
		alloc( aSize , defaultValue );
	}

	_BuiltinArray_(class_kind_t aTypeId,
			const BaseTypeSpecifier & aTypeSpecifier,
			const BaseVector & anArray)
	: BuiltinArray( aTypeId , aTypeSpecifier , anArray.size() ),
	mTable( nullptr )
	{
		alloc( anArray );
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~_BuiltinArray_()
	{
		destroyContent();

		delete[] ( mTable );

		mTable = nullptr;
	}

	inline virtual void destroyContent()
	{
//		for( std::size_t offset = 0 ; offset < mSize ; ++offset )
//		{
//			sep::destroy( mTable[offset] );
//		}
	}


	/*
	 ***************************************************************************
	 * RESET
	 ***************************************************************************
	 */

	void reset(T value)
	{
		for( std::size_t offset = 0 ; offset < mSize ; ++offset )
		{
			mTable[offset] = value;
		}
	}


	/*
	 ***************************************************************************
	 * ALLOCATION
	 ***************************************************************************
	 */

	inline void alloc(std::size_t aSize)
	{
		mSize = aSize;

		mTable = ( (mSize > 0)? (new T[ mSize ]) : nullptr );
	}


	inline void alloc(std::size_t aSize, T defaultValue)
	{
		alloc( aSize );

		for( std::size_t offset = 0 ; offset < mSize ; ++offset )
		{
			mTable[offset] = defaultValue;
		}
	}


	inline void alloc(const _BuiltinArray_ & anArray)
	{
		alloc( anArray.size() );

		for( std::size_t offset = 0 ; offset < mSize ; ++offset )
		{
//			mTable[offset] = anArray[offset];
			mTable[offset] = anArray.get(offset);
		}
	}


	inline void alloc(const BaseVector & anArray)
	{
		alloc( anArray.size() );

		for( std::size_t offset = 0 ; offset < mSize ; ++offset )
		{
			mTable[offset] = anArray[offset];
		}
	}



	/*
	 ***************************************************************************
	 * RE-ALLOCATION
	 ***************************************************************************
	 */

	inline void realloc(std::size_t aSize)
	{
		destroyContent();

		if( mSize != aSize )
		{
			delete[] ( mTable );

			alloc( aSize );
		}
	}


	inline void realloc(std::size_t aSize, T defaultValue)
	{
		destroyContent();

		if( mSize != aSize )
		{
			delete[] ( mTable );

			alloc( aSize );
		}

		reset( defaultValue );
	}


	inline void realloc(const _BuiltinArray_ & anArray)
	{
		destroyContent();

		if( mSize != anArray.size() )
		{
			delete[] ( mTable );

			alloc( anArray.size() );
		}

		for( std::size_t offset = 0 ; offset < mSize ; ++offset )
		{
			mTable[offset] = anArray[offset];
		}
	}


	inline void realloc(const BaseVector & anArray)
	{
		destroyContent();

		if( mSize != anArray.size() )
		{
			delete[] ( mTable );

			alloc( anArray.size() );
		}

		for( std::size_t offset = 0 ; offset < mSize ; ++offset )
		{
			mTable[offset] = anArray[offset];
		}
	}


	/*
	 ***************************************************************************
	 * RE-SIZE
	 ***************************************************************************
	 */

	inline void resize(std::size_t aSize) override
	{
		if( mSize > 0 )
		{
			std::size_t oldSize = mSize;
			T * oldTable = mTable;

			alloc( aSize );

			if( aSize > oldSize )
			{
				aSize = oldSize;
			}

			for( std::size_t offset = 0 ; offset < aSize ; ++offset )
			{
				mTable[offset] = oldTable[offset];
			}

			delete[] oldTable;
		}

		else
		{
			alloc(aSize);
		}
	}

	inline void resize(std::size_t aSize, T defaultValue)
	{
		if( mSize > 0 )
		{
			std::size_t oldSize = mSize;
			T * oldTable = mTable;

			alloc( aSize );

			std::size_t offset = 0;

			if( aSize > oldSize )
			{
				aSize = oldSize;
			}

			for( ; offset < aSize ; ++offset )
			{
				mTable[offset] = oldTable[offset];
			}

			for( ; offset < mSize ; ++offset )
			{
				mTable[offset] = defaultValue;
			}

			delete[] oldTable;
		}

		else
		{
			alloc(aSize, defaultValue);
		}
	}


	/**
	 * DATA
	 */
	inline T * data() const
	{
		return( mTable );
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

	inline iterator end()
	{
		return( mTable + mSize );
	}

	inline const_iterator end() const
	{
		return( mTable + mSize );
	}



	/**
	 * GETTER - SETTER
	 * mTable
	 */
//	inline const_reference at(std::size_t offset) const
//	{
//		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , mSize ) << SEND_EXIT;
//
//		return( mTable[offset] );
//	}

	inline reference get(std::size_t offset)
	{
		return( mTable[offset] );
	}


	inline const_reference get(std::size_t offset) const
	{
		return( mTable[offset] );
	}


	inline void set(std::size_t offset, T arg)
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , mSize ) << SEND_EXIT;

		mTable[offset] = arg;
	}

	inline void set(std::size_t offset, reference arg)
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , mSize ) << SEND_EXIT;

		mTable[offset] = arg;
	}

	// Due to [-Woverloaded-virtual=]
	using BuiltinArray::set;


	// operator[]
//	inline reference operator[](std::size_t offset)
//	{
//		return( mTable[offset] );
//	}
//
//	inline const_reference operator[](std::size_t offset) const
//	{
//		return( mTable[offset] );
//	}

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


	/**
	 * contains a particular element
	 */
	inline virtual bool contains(T anArray) const
	{
		for( std::size_t offset = 0 ; offset < mSize ; ++offset )
		{
			if( mTable[offset] == anArray )
			{
				return( true );
			}
		}

		return( false );
	}

	// Due to [-Woverloaded-virtual=]
	using BuiltinArray::contains;

};


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// ArrayBF
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class ArrayBF final :
		public _BuiltinArray_< BF >,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( ArrayBF )
{

	AVM_DECLARE_CLONABLE_CLASS( ArrayBF )


protected:
	/**
	 * ATTRIBUTES
	 */
	class_kind_t mElementTypeId;

	AvmInstruction * mInstruction;


public:
	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	ArrayBF(const ArrayBF & anArray);

	/**
	 * CONSTRUCTOR
	 * Other
	 */
	ArrayBF(const BFVector & anArray);

	ArrayBF(const BaseTypeSpecifier & aTypeSpecifier, const BFVector & aVector)
	: _BuiltinArray_< BF >(CLASS_KIND_T( ArrayBF ), aTypeSpecifier, aVector),
	mElementTypeId( ClassKindInfoInitializer::TYPE_UNDEFINED_ID ),
	mInstruction( nullptr )
	{
		//!!! NOTHING
	}

	ArrayBF(const BaseTypeSpecifier & aTypeSpecifier, std::size_t aSize = 0)
	: _BuiltinArray_< BF >(CLASS_KIND_T( ArrayBF ), aTypeSpecifier, aSize),
	mElementTypeId( ClassKindInfoInitializer::TYPE_UNDEFINED_ID ),
	mInstruction( nullptr )
	{
		//!!! NOTHING
	}


	ArrayBF(class_kind_t eltTypeId,
			const BaseTypeSpecifier & aTypeSpecifier, std::size_t aSize = 0)
	: _BuiltinArray_< BF >(CLASS_KIND_T( ArrayBF ), aTypeSpecifier, aSize),
	mElementTypeId( eltTypeId ),
	mInstruction( nullptr )
	{
		//!!! NOTHING
	}


	ArrayBF(const BaseTypeSpecifier & aTypeSpecifier,
			std::size_t aSize, const BF & defaultValue)
	: _BuiltinArray_< BF >(CLASS_KIND_T( ArrayBF ),	aTypeSpecifier, aSize ),
	mElementTypeId( defaultValue.classKind() ),
	mInstruction( nullptr )
	{
		setAll( defaultValue );
	}

	ArrayBF(const BaseTypeSpecifier & aTypeSpecifier, const BF & defaultValue);

	/**
	 * DESTRUCTOR
	 */
	virtual ~ArrayBF()
	{
		delete[] ( mTable );

		mSize = 0;
		mTable = nullptr;
	}


	/**
	 * INTERFACE
	 */
	bool contains(const BF & arg) const override;

	bool startsWith(const ArrayBF & other) const;

	bool endsWith(const ArrayBF & other) const;


	/**
	 * TRIVIALLY EQUAL
	 */
	bool isTEQ(const ArrayBF & other) const;

	// Due to [-Woverloaded-virtual=]
	using BuiltinArray::isTEQ;


	inline bool isNTEQ(const ArrayBF & other) const
	{
		return( not ArrayBF::isTEQ( other ) );
	}

	// Due to [-Woverloaded-virtual=]
	using BuiltinArray::isNTEQ;

	/**
	 * USUAL EQUAL
	 */
	int compare(const ArrayBF & other) const;

	bool isEQ(const ArrayBF & other) const;

	// Due to [-Woverloaded-virtual=]
	using BuiltinArray::isEQ;

	inline bool isNEQ(const ArrayBF & other) const
	{
		return( not isEQ( other ) );
	}

	// Due to [-Woverloaded-virtual=]
	using BuiltinArray::isNEQ;

	/**
	 * SYNTAXIC EQUAL
	 */
	bool isSEQ(const ArrayBF & other) const;

	inline bool isNSEQ(const ArrayBF & other) const
	{
		return( not ArrayBF::isSEQ( other ) );
	}


	/**
	 * GETTER - SETTER
	 * for container of BF
	 */
	inline virtual BF & at(std::size_t offset) override
	{
//		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , mSize ) << SEND_EXIT;

		return( mTable[offset] );
	}

	inline virtual const BF & at(std::size_t offset) const override final
	{
//		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , mSize ) << SEND_EXIT;

		return( mTable[offset] );
	}


	inline BF & operator[](std::size_t offset) override
	{
		return( mTable[offset] );
	}

	inline const BF & operator[](std::size_t offset) const override
	{
		return( mTable[offset] );
	}


	inline virtual BF & get(std::size_t offset)
	{
//		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , mSize ) << SEND_EXIT;

		return( mTable[offset] );
	}

	inline virtual const BF & get(std::size_t offset) const
	{
//		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , mSize ) << SEND_EXIT;

		return( mTable[offset] );
	}


	inline virtual BF & getWritable(std::size_t offset) override
	{
//		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , mSize ) << SEND_EXIT;

		mTable[offset].makeWritable();

		return( mTable[offset] );
	}

	inline virtual void makeWritable(std::size_t offset) override
	{
//		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , mSize ) << SEND_EXIT;

		mTable[offset].makeWritable();
	}


	inline void set(std::size_t offset, const BF & arg) override
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , mSize ) << SEND_EXIT;

		if( (mElementTypeId != ClassKindInfoInitializer::TYPE_UNDEFINED_ID)
			&& (mElementTypeId != arg.classKind()) )
		{
			mElementTypeId = ClassKindInfoInitializer::TYPE_UNDEFINED_ID;
		}

		mTable[offset] = arg;
	}

	inline void setAll(const BF & arg)
	{
		for( std::size_t offset = 0 ; offset < mSize ; ++offset )
		{
			mTable[offset] = arg;
		}
	}


	/**
	 * GETTER - SETTER
	 * mElementTypeId
	 */
	inline virtual class_kind_t getElementTypeId() const
	{
		return( mElementTypeId );
	}

	inline void setElementTypeId(class_kind_t aTypeId)
	{
		mElementTypeId = aTypeId;
	}


	// CAST
	ArrayBF * getArrayBF() const override
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "Unexpected invocation of ArrayBF::getArrayBF() !!!"
				<< SEND_EXIT;

		return( const_cast< ArrayBF * >( this ) );
	}

	// COPY
	void copy(BuiltinArray * intputArray, std::size_t count);


	/**
	 * GETTER - SETTER
	 * for mInstruction
	 */
	inline AvmInstruction * getInstruction() const
	{
		return( mInstruction );
	}

	inline bool hasInstruction() const
	{
		return( mInstruction != nullptr );
	}

	inline void setInstruction(AvmInstruction * anInstruction)
	{
		mInstruction = anInstruction;
	}


	/**
	 ***************************************************************************
	 * SERIALIZATION
	 ***************************************************************************
	 */
	inline virtual std::string str(std::size_t offset) const override
	{
		return( mTable[offset].str() );
	}

	virtual std::string str() const override;


	virtual void toStream(OutStream & os) const override;

};


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// Array of Builtin Type
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class ArrayInteger :
		public _BuiltinArray_< avm_integer_t >,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( ArrayInteger )
{

	AVM_DECLARE_CLONABLE_CLASS( ArrayInteger )


public:

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	ArrayInteger(const ArrayInteger & anArray)
	: _BuiltinArray_< avm_integer_t >( anArray )
	{
	//!!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Other
	 */
	ArrayInteger(std::size_t aSize = 0);


	// CAST
	ArrayBF * getArrayBF() const override;


	/**
	 ***************************************************************************
	 * SERIALIZATION
	 ***************************************************************************
	 */
	inline virtual std::string str(std::size_t offset) const override
	{
		return( OSS() << mTable[offset] );
	}

	inline void toStream(OutStream & os) const override
	{
		os << TAB << /*"%i"*/ "[ ";
		if( mSize > 0 )
		{
			os << mTable[0];
			for( std::size_t offset = 1 ; offset < mSize ; ++offset )
			{
				os << " , " << mTable[offset];
			}
		}
		os << " ]" << EOL_FLUSH;
	}

}; // end class ArrayInteger



class ArrayRational :
		public _BuiltinArray_< Pair< avm_integer_t , avm_integer_t > >,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( ArrayRational )
{

	AVM_DECLARE_CLONABLE_CLASS( ArrayRational )

	/**
	 * TYPEDEF
	 */
	typedef Pair< avm_integer_t , avm_integer_t >  PairInteger;


public:

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	ArrayRational(const ArrayRational & anArray)
	: _BuiltinArray_< PairInteger >( anArray )
	{
	//!!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Other
	 */
	ArrayRational(std::size_t aSize = 0);


	// CAST
	ArrayBF * getArrayBF() const override;


	inline void set(std::size_t offset,
			avm_integer_t aNumer, avm_integer_t aDenom)
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , mSize ) << SEND_EXIT;

		mTable[offset] = PairInteger(aNumer, aDenom);
	}

	// Due to [-Woverloaded-virtual=]
	using BuiltinArray::set;

	/**
	 ***************************************************************************
	 * SERIALIZATION
	 ***************************************************************************
	 */
	inline virtual std::string str(std::size_t offset) const override
	{
		return( OSS()  << mTable[offset].first()
				<< '/' << mTable[offset].second() );
	}

	inline void toStream(OutStream & os) const override
	{
		os << TAB << /*"%r"*/ "[ ";
		if( mSize > 0 )
		{
			os << mTable[0].first() << '/' << mTable[0].second();
			for( std::size_t offset = 1 ; offset < mSize ; ++offset )
			{
				os << " , " << mTable[offset].first()
						<< '/' << mTable[offset].second();
			}
		}
		os << " ]" << EOL_FLUSH;
	}

}; // end class ArrayRational



class ArrayFloat :
		public _BuiltinArray_< avm_float_t >,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( ArrayFloat )
{

	AVM_DECLARE_CLONABLE_CLASS( ArrayFloat )


public:

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	ArrayFloat(const ArrayFloat & anArray)
	: _BuiltinArray_< double >( anArray )
	{
	//!!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Other
	 */
	ArrayFloat(std::size_t aSize = 0);


	// CAST
	ArrayBF * getArrayBF() const override;


	/**
	 ***************************************************************************
	 * SERIALIZATION
	 ***************************************************************************
	 */
	inline virtual std::string str(std::size_t offset) const override
	{
		return( OSS() << mTable[offset] );
	}

	inline void toStream(OutStream & os) const override
	{
		os << TAB << /*"%f"*/ "[ ";
		if( mSize > 0 )
		{
			os << mTable[0];
			for( std::size_t offset = 1 ; offset < mSize ; ++offset )
			{
				os << " , " << mTable[offset];
			}
		}
		os << " ]" << EOL_FLUSH;
	}

}; // end class ArrayFloat



class ArrayBoolean :
		public _BuiltinArray_< bool >,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( ArrayBoolean )
{

	AVM_DECLARE_CLONABLE_CLASS( ArrayBoolean )


public:

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	ArrayBoolean(const ArrayBoolean & anArray)
	: _BuiltinArray_< bool >( anArray )
	{
	//!!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Other
	 */
	ArrayBoolean(std::size_t aSize = 0);


	// CAST
	ArrayBF * getArrayBF() const override;


	/**
	 ***************************************************************************
	 * SERIALIZATION
	 ***************************************************************************
	 */
	inline virtual std::string str(std::size_t offset) const override
	{
		return( mTable[offset] ? "true" : "false" );
	}

	inline void toStream(OutStream & os) const override
	{
		os << TAB << /*"%b"*/ "[ ";
		if( mSize > 0 )
		{
			os << (mTable[0] ? "true" : "false");
			for( std::size_t offset = 1 ; offset < mSize ; ++offset )
			{
				os << " , " << (mTable[offset] ? "true" : "false");
			}
		}
		os << " ]" << EOL_FLUSH;
	}

}; // end class ArrayBoolean



class ArrayCharacter :
		public _BuiltinArray_< char >,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( ArrayCharacter )
{

	AVM_DECLARE_CLONABLE_CLASS( ArrayCharacter )


public:

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	ArrayCharacter(const ArrayCharacter & anArray)
	: _BuiltinArray_< char >( anArray )
	{
	//!!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Other
	 */
	ArrayCharacter(std::size_t aSize = 0);


	// CAST
	ArrayBF * getArrayBF() const override;


	/**
	 ***************************************************************************
	 * SERIALIZATION
	 ***************************************************************************
	 */
	inline virtual std::string str(std::size_t offset) const override
	{
		return( OSS() << mTable[offset] );
	}

	inline void toStream(OutStream & os) const override
	{
		os << TAB << /*"%c"*/ "[ ";
		if( mSize > 0 )
		{
			os << "'" << mTable[0] << "'";

			for( std::size_t offset = 1 ; offset < mSize ; ++offset )
			{
				os << " , '" << mTable[offset] << "'";
			}
		}
		os << " ]" << EOL_FLUSH;
	}
}; // end class ArrayCharacter



class ArrayString :
		public _BuiltinArray_< std::string >,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( ArrayString )
{

	AVM_DECLARE_CLONABLE_CLASS( ArrayString )


public:

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	ArrayString(const ArrayString & anArray)
	: _BuiltinArray_< std::string >( anArray )
	{
	//!!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Other
	 */
	ArrayString(std::size_t aSize = 0);


	// CAST
	ArrayBF * getArrayBF() const override;


	/**
	 ***************************************************************************
	 * SERIALIZATION
	 ***************************************************************************
	 */
	inline virtual std::string str(std::size_t offset) const override
	{
		return( OSS() << "\"" << mTable[offset] << "\"" );
//		return( OSS() << mTable[offset] );
	}

	inline void toStream(OutStream & os) const override
	{
		os << TAB << /*"%s"*/ "[ ";
		if( mSize > 0 )
		{
			os << "\"" << mTable[0] << "\"";

			for( std::size_t offset = 1 ; offset < mSize ; ++offset )
			{
				os << " , \"" << mTable[offset] << "\"";
			}
		}
		os << " ]" << EOL_FLUSH;
	}
}; // end class ArrayString



class ArrayIdentifier :
		public _BuiltinArray_< std::string >,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( ArrayIdentifier )
{

	AVM_DECLARE_CLONABLE_CLASS( ArrayIdentifier )


public:

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	ArrayIdentifier(const ArrayIdentifier & anArray)
	: _BuiltinArray_< std::string >( anArray )
	{
	//!!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Other
	 */
	ArrayIdentifier(std::size_t aSize = 0);


	// CAST
	ArrayBF * getArrayBF() const override;


	/**
	 ***************************************************************************
	 * SERIALIZATION
	 ***************************************************************************
	 */
	inline virtual std::string str(std::size_t offset) const override
	{
		return( OSS() << mTable[offset] );
	}

	inline void toStream(OutStream & os) const override
	{
		os << TAB << /*"%id"*/ "[ ";
		if( mSize > 0 )
		{
			os << mTable[0];
			for( std::size_t offset = 1 ; offset < mSize ; ++offset )
			{
				os << " , " << mTable[offset];
			}
		}
		os << " ]" << EOL_FLUSH;
	}

}; // end class ArrayIdentifier



class ArrayQualifiedIdentifier :
		public _BuiltinArray_< std::string >,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( ArrayQualifiedIdentifier )
{

	AVM_DECLARE_CLONABLE_CLASS( ArrayQualifiedIdentifier )


public:

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	ArrayQualifiedIdentifier(const ArrayQualifiedIdentifier & anArray)
	: _BuiltinArray_< std::string >( anArray )
	{
	//!!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Other
	 */
	ArrayQualifiedIdentifier(std::size_t aSize = 0);


	// CAST
	ArrayBF * getArrayBF() const override;


	/**
	 ***************************************************************************
	 * SERIALIZATION
	 ***************************************************************************
	 */
	inline virtual std::string str(std::size_t offset) const override
	{
		return( OSS() << mTable[offset] );
	}

	inline void toStream(OutStream & os) const override
	{
		os << TAB << /*"%ufi"*/ "[ ";
		if( mSize > 0 )
		{
			os << mTable[0];
			for( std::size_t offset = 1 ; offset < mSize ; ++offset )
			{
				os << " , " << mTable[offset];
			}
		}
		os << " ]" << EOL_FLUSH;
	}

}; // end class ArrayQualifiedIdentifier


}

#endif /* BUILTINARRAY_H_ */
