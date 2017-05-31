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
	BaseTypeSpecifier * mTypeSpecifier;

	avm_size_t mSize;


public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BuiltinArray(class_kind_t aTypeId,
			BaseTypeSpecifier * aTypeSpecifier, avm_size_t aSize = 0)
	: BuiltinCollection( aTypeId ),
	mTypeSpecifier( aTypeSpecifier ),
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
	inline BaseTypeSpecifier * getTypeSpecifier() const
	{
		return( mTypeSpecifier );
	}

	inline avm_type_specifier_kind_t getTypeSpecifierKind() const
	{
		return( (mTypeSpecifier != NULL) ?
				mTypeSpecifier->getTypeSpecifierKind() : TYPE_NULL_SPECIFIER );
	}

	inline bool hasTypeSpecifier() const
	{
		return( mTypeSpecifier != NULL );
	}


	inline void setTypeSpecifier(BaseTypeSpecifier * aTypeSpecifier)
	{
		mTypeSpecifier = aTypeSpecifier;
	}


	// size is constant
	inline avm_size_t size() const
	{
		return( mSize );
	}

	inline avm_size_t capacity() const
	{
		return( mSize );
	}

	inline void setCapacity(long aCapacity)
	{
		AVM_OS_FATAL_ERROR_EXIT << "NO SENSE HERE !!!" << SEND_EXIT;
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



	inline virtual bool contains(const BF & arg) const
	{
		return( false );
	}


	// CAST
	virtual ArrayBF * getArrayBF() = 0;


	static class_kind_t getArrayTypeId(class_kind_t aTypeId);

	static class_kind_t getArrayTypeId(
			class_kind_t classKindA, class_kind_t classKindB);

	static BF create(const BFVector & array);


	/**
	 * Serialization
	 */
	virtual std::string str(avm_size_t offset) const = 0;

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
	_BuiltinArray_(class_kind_t aTypeId, BaseTypeSpecifier * aTypeSpecifier,
			avm_size_t aSize = 0)
	: BuiltinArray( aTypeId , aTypeSpecifier, aSize ),
	mTable( NULL )
	{
		alloc( aSize );
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	_BuiltinArray_(const _BuiltinArray_ & anArray)
	: BuiltinArray( anArray ),
	mTable( NULL )
	{
		alloc( anArray );
	}


	/**
	 * CONSTRUCTOR
	 * Other
	 */
	_BuiltinArray_(class_kind_t aTypeId, BaseTypeSpecifier * aTypeSpecifier,
			avm_size_t aSize, T defaultValue)
	: BuiltinArray( aTypeId , aTypeSpecifier , aSize ),
	mTable( NULL )
	{
		alloc( aSize , defaultValue );
	}

	_BuiltinArray_(class_kind_t aTypeId, BaseTypeSpecifier * aTypeSpecifier,
			const BaseVector & anArray)
	: BuiltinArray( aTypeId , aTypeSpecifier , anArray.size() ),
	mTable( NULL )
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

		mTable = NULL;
	}

	inline virtual void destroyContent()
	{
//		for( avm_size_t offset = 0 ; offset < mSize ; ++offset )
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


	inline void alloc(const _BuiltinArray_ & anArray)
	{
		alloc( anArray.size() );

		for( avm_size_t offset = 0 ; offset < mSize ; ++offset )
		{
//			mTable[offset] = anArray[offset];
			mTable[offset] = anArray.get(offset);
		}
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
		destroyContent();

		if( mSize != aSize )
		{
			delete[] ( mTable );

			alloc( aSize );
		}
	}


	inline void realloc(avm_size_t aSize, T defaultValue)
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

		for( avm_size_t offset = 0 ; offset < mSize ; ++offset )
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

			delete[] oldTable;
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

			avm_size_t offset = 0;

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
//	inline const_reference at(avm_size_t offset) const
//	{
//		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , mSize ) << SEND_EXIT;
//
//		return( mTable[offset] );
//	}

	inline reference get(avm_size_t offset)
	{
		return( mTable[offset] );
	}


	inline const_reference get(avm_size_t offset) const
	{
		return( mTable[offset] );
	}


	inline void set(avm_size_t offset, T arg)
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , mSize ) << SEND_EXIT;

		mTable[offset] = arg;
	}

	inline void set(avm_size_t offset, reference arg)
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , mSize ) << SEND_EXIT;

		mTable[offset] = arg;
	}



	// operator[]
//	inline reference operator[](avm_size_t offset)
//	{
//		return( mTable[offset] );
//	}
//
//	inline const_reference operator[](avm_size_t offset) const
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
		for( avm_size_t offset = 0 ; offset < mSize ; ++offset )
		{
			if( mTable[offset] == anArray )
			{
				return( true );
			}
		}

		return( false );
	}

};


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// ArrayBF
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class ArrayBF :
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

	ArrayBF(BaseTypeSpecifier * aTypeSpecifier, const BFVector & aVector)
	: _BuiltinArray_< BF >(CLASS_KIND_T( ArrayBF ), aTypeSpecifier, aVector),
	mElementTypeId( ClassKindInfoInitializer::TYPE_UNDEFINED_ID ),
	mInstruction( NULL )
	{
		//!!! NOTHING
	}

	ArrayBF(BaseTypeSpecifier * aTypeSpecifier, avm_size_t aSize = 0)
	: _BuiltinArray_< BF >(CLASS_KIND_T( ArrayBF ), aTypeSpecifier, aSize),
	mElementTypeId( ClassKindInfoInitializer::TYPE_UNDEFINED_ID ),
	mInstruction( NULL )
	{
		//!!! NOTHING
	}


	ArrayBF(class_kind_t eltTypeId, BaseTypeSpecifier * aTypeSpecifier,
			avm_size_t aSize = 0)
	: _BuiltinArray_< BF >(CLASS_KIND_T( ArrayBF ), aTypeSpecifier, aSize),
	mElementTypeId( eltTypeId ),
	mInstruction( NULL )
	{
		//!!! NOTHING
	}


	ArrayBF(BaseTypeSpecifier * aTypeSpecifier, avm_size_t aSize,
			const BF & defaultValue)
	: _BuiltinArray_< BF >(CLASS_KIND_T( ArrayBF ),	aTypeSpecifier, aSize ),
	mElementTypeId( defaultValue.classKind() ),
	mInstruction( NULL )
	{
		setAll( defaultValue );
	}

	ArrayBF(BaseTypeSpecifier * aTypeSpecifier, const BF & defaultValue);

	/**
	 * DESTRUCTOR
	 */
	virtual ~ArrayBF()
	{
		delete[] ( mTable );

		mSize = 0;
		mTable = NULL;
	}


	/**
	 * INTERFACE
	 */
	bool contains(const BF & arg) const;

	bool startsWith(const ArrayBF & other) const;

	bool endsWith(const ArrayBF & other) const;


	/**
	 * TRIVIALLY EQUAL
	 */
	bool isTEQ(const ArrayBF & other) const;

	inline bool isNTEQ(const ArrayBF & other) const
	{
		return( not ArrayBF::isTEQ( other ) );
	}

	/**
	 * USUAL EQUAL
	 */
	int compare(const ArrayBF & other) const;

	bool isEQ(const ArrayBF & other) const;

	inline bool isNEQ(const ArrayBF & other) const
	{
		return( not isEQ( other ) );
	}

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
	inline virtual BF & at(avm_size_t offset)
	{
//		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , mSize ) << SEND_EXIT;

		return( mTable[offset] );
	}

	inline virtual const BF & at(avm_size_t offset) const
	{
//		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , mSize ) << SEND_EXIT;

		return( mTable[offset] );
	}


	inline BF & operator[](avm_size_t offset)
	{
		return( mTable[offset] );
	}

	inline const BF & operator[](avm_size_t offset) const
	{
		return( mTable[offset] );
	}


	inline virtual BF & get(avm_size_t offset)
	{
//		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , mSize ) << SEND_EXIT;

		return( mTable[offset] );
	}

	inline virtual const BF & get(avm_size_t offset) const
	{
//		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , mSize ) << SEND_EXIT;

		return( mTable[offset] );
	}


	inline virtual BF & getWritable(avm_size_t offset)
	{
//		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , mSize ) << SEND_EXIT;

		mTable[offset].makeWritable();

		return( mTable[offset] );
	}

	inline virtual void makeWritable(avm_size_t offset)
	{
//		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , mSize ) << SEND_EXIT;

		mTable[offset].makeWritable();
	}


	inline void set(avm_size_t offset, const BF & arg)
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
		for( avm_size_t offset = 0 ; offset < mSize ; ++offset )
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
	ArrayBF * getArrayBF()
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "Unexpected invocation of ArrayBF::getArrayBF() !!!"
				<< SEND_EXIT;

		return( this );
	}

	// COPY
	void copy(BuiltinArray * intputArray, avm_size_t count);


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
		return( mInstruction != NULL );
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
	inline virtual std::string str(avm_size_t offset) const
	{
		return( mTable[offset].str() );
	}

	virtual std::string str() const;


	virtual void toStream(OutStream & os) const;

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
	ArrayInteger(avm_size_t aSize = 0);


	// CAST
	ArrayBF * getArrayBF();


	/**
	 ***************************************************************************
	 * SERIALIZATION
	 ***************************************************************************
	 */
	inline virtual std::string str(avm_size_t offset) const
	{
		return( OSS() << mTable[offset] );
	}

	inline void toStream(OutStream & os) const
	{
		os << TAB << /*"%i"*/ "[ ";
		if( mSize > 0 )
		{
			os << mTable[0];
			for( avm_size_t offset = 1 ; offset < mSize ; ++offset )
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
	ArrayRational(avm_size_t aSize = 0);


	// CAST
	ArrayBF * getArrayBF();


	inline void set(avm_size_t offset,
			avm_integer_t aNumer, avm_integer_t aDenom)
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , mSize ) << SEND_EXIT;

		mTable[offset] = PairInteger(aNumer, aDenom);
	}

	/**
	 ***************************************************************************
	 * SERIALIZATION
	 ***************************************************************************
	 */
	inline virtual std::string str(avm_size_t offset) const
	{
		return( OSS()  << mTable[offset].first()
				<< '/' << mTable[offset].second() );
	}

	inline void toStream(OutStream & os) const
	{
		os << TAB << /*"%r"*/ "[ ";
		if( mSize > 0 )
		{
			os << mTable[0].first() << '/' << mTable[0].second();
			for( avm_size_t offset = 1 ; offset < mSize ; ++offset )
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
	ArrayFloat(avm_size_t aSize = 0);


	// CAST
	ArrayBF * getArrayBF();


	/**
	 ***************************************************************************
	 * SERIALIZATION
	 ***************************************************************************
	 */
	inline virtual std::string str(avm_size_t offset) const
	{
		return( OSS() << mTable[offset] );
	}

	inline void toStream(OutStream & os) const
	{
		os << TAB << /*"%f"*/ "[ ";
		if( mSize > 0 )
		{
			os << mTable[0];
			for( avm_size_t offset = 1 ; offset < mSize ; ++offset )
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
	ArrayBoolean(avm_size_t aSize = 0);


	// CAST
	ArrayBF * getArrayBF();


	/**
	 ***************************************************************************
	 * SERIALIZATION
	 ***************************************************************************
	 */
	inline virtual std::string str(avm_size_t offset) const
	{
		return( mTable[offset] ? "true" : "false" );
	}

	inline void toStream(OutStream & os) const
	{
		os << TAB << /*"%b"*/ "[ ";
		if( mSize > 0 )
		{
			os << (mTable[0] ? "true" : "false");
			for( avm_size_t offset = 1 ; offset < mSize ; ++offset )
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
	ArrayCharacter(avm_size_t aSize = 0);


	// CAST
	ArrayBF * getArrayBF();


	/**
	 ***************************************************************************
	 * SERIALIZATION
	 ***************************************************************************
	 */
	inline virtual std::string str(avm_size_t offset) const
	{
		return( OSS() << mTable[offset] );
	}

	inline void toStream(OutStream & os) const
	{
		os << TAB << /*"%c"*/ "[ ";
		if( mSize > 0 )
		{
			os << "'" << mTable[0] << "'";

			for( avm_size_t offset = 1 ; offset < mSize ; ++offset )
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
	ArrayString(avm_size_t aSize = 0);


	// CAST
	ArrayBF * getArrayBF();


	/**
	 ***************************************************************************
	 * SERIALIZATION
	 ***************************************************************************
	 */
	inline virtual std::string str(avm_size_t offset) const
	{
		return( OSS() << "\"" << mTable[offset] << "\"" );
//		return( OSS() << mTable[offset] );
	}

	inline void toStream(OutStream & os) const
	{
		os << TAB << /*"%s"*/ "[ ";
		if( mSize > 0 )
		{
			os << "\"" << mTable[0] << "\"";

			for( avm_size_t offset = 1 ; offset < mSize ; ++offset )
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
	ArrayIdentifier(avm_size_t aSize = 0);


	// CAST
	ArrayBF * getArrayBF();


	/**
	 ***************************************************************************
	 * SERIALIZATION
	 ***************************************************************************
	 */
	inline virtual std::string str(avm_size_t offset) const
	{
		return( OSS() << mTable[offset] );
	}

	inline void toStream(OutStream & os) const
	{
		os << TAB << /*"%id"*/ "[ ";
		if( mSize > 0 )
		{
			os << mTable[0];
			for( avm_size_t offset = 1 ; offset < mSize ; ++offset )
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
	ArrayQualifiedIdentifier(avm_size_t aSize = 0);


	// CAST
	ArrayBF * getArrayBF();


	/**
	 ***************************************************************************
	 * SERIALIZATION
	 ***************************************************************************
	 */
	inline virtual std::string str(avm_size_t offset) const
	{
		return( OSS() << mTable[offset] );
	}

	inline void toStream(OutStream & os) const
	{
		os << TAB << /*"%ufi"*/ "[ ";
		if( mSize > 0 )
		{
			os << mTable[0];
			for( avm_size_t offset = 1 ; offset < mSize ; ++offset )
			{
				os << " , " << mTable[offset];
			}
		}
		os << " ]" << EOL_FLUSH;
	}

}; // end class ArrayQualifiedIdentifier


}

#endif /* BUILTINARRAY_H_ */
