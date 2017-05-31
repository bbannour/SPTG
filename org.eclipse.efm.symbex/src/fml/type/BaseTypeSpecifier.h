/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 7 août 2008
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef BASETYPESPECIFIER_H_
#define BASETYPESPECIFIER_H_

#include <common/AvmPointer.h>
#include <common/BF.h>

#include <fml/common/ObjectElement.h>

#include <fml/executable/BaseCompiledForm.h>

#include <fml/expression/AvmCode.h>

#include <fml/infrastructure/DataType.h>

#include <fml/lib/ITypeSpecifier.h>


namespace sep
{

class ArrayBF;


class BaseTypeSpecifier :
		public BaseCompiledForm,
		public ITypeSpecifier,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( BaseTypeSpecifier )
{

	AVM_DECLARE_CLONABLE_CLASS( BaseTypeSpecifier )


protected:
	/*
	 * ATTRIBUTES
	 */
	avm_type_specifier_kind_t mSpecifierKind;

	avm_size_t mMinimumSize;
	avm_size_t mMaximumSize;


	avm_size_t mDataSize;

	avm_size_t mBitSize;

	BF mDefaultValue;

	BF mConstraint;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BaseTypeSpecifier(avm_type_specifier_kind_t aSpecifierKind,
			const std::string & aTypeID, avm_size_t maxSize,
			avm_size_t aDataSize, avm_size_t aBitSize, const BF & defaultValue)
	: BaseCompiledForm(CLASS_KIND_T( BaseTypeSpecifier ), aTypeID, aTypeID),
	mSpecifierKind( aSpecifierKind ),
	mMinimumSize( 0 ),
	mMaximumSize( maxSize ),
	mDataSize( aDataSize ),
	mBitSize( aBitSize ),
	mDefaultValue( defaultValue ),
	mConstraint( )
	{
		//!! NOTHING
	}

	BaseTypeSpecifier(avm_type_specifier_kind_t aSpecifierKind,
			const std::string & aTypeID, avm_size_t minSize, avm_size_t maxSize,
			avm_size_t aDataSize, avm_size_t aBitSize, const BF & defaultValue)
	: BaseCompiledForm(CLASS_KIND_T( BaseTypeSpecifier ), aTypeID, aTypeID),
	mSpecifierKind( aSpecifierKind ),
	mMinimumSize( minSize ),
	mMaximumSize( maxSize ),
	mDataSize( aDataSize ),
	mBitSize( aBitSize ),
	mDefaultValue( defaultValue ),
	mConstraint( )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * copy
	 */
	BaseTypeSpecifier(const BaseTypeSpecifier & aTypeSpecifier)
	: BaseCompiledForm( aTypeSpecifier ),
	mSpecifierKind( aTypeSpecifier.mSpecifierKind ),
	mMinimumSize( aTypeSpecifier.mMinimumSize ),
	mMaximumSize( aTypeSpecifier.mMaximumSize ),
	mDataSize( aTypeSpecifier.mDataSize ),
	mBitSize( aTypeSpecifier.mBitSize ),
	mDefaultValue( aTypeSpecifier.mDefaultValue ),
	mConstraint( aTypeSpecifier.mConstraint )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Others
	 */
	BaseTypeSpecifier(class_kind_t aClassKind,
			avm_type_specifier_kind_t aSpecifierKind,
			const DataType * aCompiledType, BaseTypeSpecifier * aTypeSpecifier)
	: BaseCompiledForm( aClassKind, NULL, aCompiledType ),
	mSpecifierKind( aSpecifierKind ),
	mMinimumSize( aTypeSpecifier->mMinimumSize ),
	mMaximumSize( aTypeSpecifier->mMaximumSize ),
	mDataSize( aTypeSpecifier->mDataSize ),
	mBitSize( aTypeSpecifier->mBitSize ),
	mDefaultValue( aTypeSpecifier->mDefaultValue ),
	mConstraint( aTypeSpecifier->mConstraint )
	{
		updateFullyQualifiedNameID();
	}

	BaseTypeSpecifier(avm_type_specifier_kind_t aSpecifierKind,
			const DataType * aCompiledType, avm_size_t maxSize,
			avm_size_t aDataSize, avm_size_t aBitSize, const BF & defaultValue)
	: BaseCompiledForm(CLASS_KIND_T( BaseTypeSpecifier ), NULL, aCompiledType),
	mSpecifierKind( aSpecifierKind ),
	mMinimumSize( 0 ),
	mMaximumSize( maxSize ),
	mDataSize( aDataSize ),
	mBitSize( aBitSize ),
	mDefaultValue( defaultValue ),
	mConstraint( )
	{
		updateFullyQualifiedNameID();
	}

	BaseTypeSpecifier(class_kind_t aClassKind,
			avm_type_specifier_kind_t aSpecifierKind,
			const ObjectElement * aCompiledType, avm_size_t maxSize,
			avm_size_t aDataSize, avm_size_t aBitSize)
	: BaseCompiledForm(aClassKind, NULL, aCompiledType),
	mSpecifierKind( aSpecifierKind ),
	mMinimumSize( 0 ),
	mMaximumSize( maxSize ),
	mDataSize( aDataSize ),
	mBitSize( aBitSize ),
	mDefaultValue( ),
	mConstraint( )
	{
		updateFullyQualifiedNameID();
	}

	BaseTypeSpecifier(class_kind_t aClassKind,
			avm_type_specifier_kind_t aSpecifierKind,
			const std::string & aTypeID, avm_size_t maxSize,
			avm_size_t aDataSize, avm_size_t aBitSize)
	: BaseCompiledForm(aClassKind, aTypeID, aTypeID),
	mSpecifierKind( aSpecifierKind ),
	mMinimumSize( 0 ),
	mMaximumSize( maxSize ),
	mDataSize( aDataSize ),
	mBitSize( aBitSize ),
	mDefaultValue( ),
	mConstraint( )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~BaseTypeSpecifier()
	{
		//!! NOTHING
	}


	/**
	 * GETTER
	 * Compiled ObjectElement as Compiled Machine
	 */
	inline const DataType * getAstDataType() const
	{
		return( getAstElement()->as< DataType >() );
	}

	/**
	 * GETTER - SETTER
	 * mSpecifierKind
	 */
	inline virtual const BaseTypeSpecifier * thisTypeSpecifier() const
	{
		return( this );
	}

	inline virtual avm_type_specifier_kind_t getTypeSpecifierKind() const
	{
		return( mSpecifierKind );
	}

	inline virtual bool isTypeSpecifierKind(
			avm_type_specifier_kind_t aSpecifierKind) const
	{
		return( mSpecifierKind == aSpecifierKind );
	}

	inline virtual bool isTypeSpecifierKind(BaseTypeSpecifier * aType) const
	{
		return( mSpecifierKind == aType->mSpecifierKind );
	}

	inline virtual bool hasTypeSpecifierKind(
			avm_type_specifier_kind_t aSpecifierKind1,
			avm_type_specifier_kind_t aSpecifierKind2) const
	{
		return( (mSpecifierKind == aSpecifierKind1) ||
				(mSpecifierKind == aSpecifierKind2) );
	}

	inline virtual bool hasTypeSpecifierKind(
			avm_type_specifier_kind_t aSpecifierKind1,
			avm_type_specifier_kind_t aSpecifierKind2,
			avm_type_specifier_kind_t aSpecifierKind3) const
	{
		return( (mSpecifierKind == aSpecifierKind1) ||
				(mSpecifierKind == aSpecifierKind2) ||
				(mSpecifierKind == aSpecifierKind3) );
	}

	inline void setSpecifierKind(avm_type_specifier_kind_t aSpecifierKind)
	{
		mSpecifierKind = aSpecifierKind;
	}


	/**
	 * SETTER
	 * mFullyQualifiedNameID
	 */
	virtual void updateFullyQualifiedNameID();


	/**
	 * GETTER - SETTER
	 * mMinimumSize
	 */
	inline avm_size_t getMinimumSize() const
	{
		return( mMinimumSize );
	}

	inline void setMinimumSize(avm_size_t minSize)
	{
		mMinimumSize = minSize;
	}

	/**
	 * GETTER - SETTER
	 * mMaximumSize
	 */
	inline avm_size_t getMaximumSize() const
	{
		return( mMaximumSize );
	}

	inline void setMaximumSize(avm_size_t maxSize)
	{
		mMaximumSize = maxSize;
	}


	inline avm_size_t size() const
	{
		return( mMaximumSize );
	}

	inline void setSize(avm_size_t maxSize)
	{
		mMaximumSize = maxSize;
	}

	/**
	 * SETTER
	 * mMinimumSize
	 * mMaximumSize
	 */
	inline void setSize(avm_size_t minSize, avm_size_t maxSize)
	{
		mMinimumSize = minSize;
		mMaximumSize = maxSize;
	}


	/**
	 * GETTER - SETTER
	 * mDataSize
	 */
	inline avm_size_t getDataSize() const
	{
		return( mDataSize );
	}

	inline void setDataSize(avm_size_t aDataSize)
	{
		mDataSize = aDataSize;
	}

	/**
	 * GETTER - SETTER
	 * mBitSize
	 */
	inline avm_size_t getBitSize() const
	{
		return( mBitSize );
	}

	inline void setBitSize(avm_size_t aBitSize)
	{
		mBitSize = aBitSize;
	}


	/**
	 * SETTER
	 * mDataSize
	 */
	inline virtual void updateSize()
	{
		AVM_OS_EXIT( FAILED )
				<< "Unexpected call of pure virtual method !!!"
				<< SEND_EXIT;
	}


	/**
	 * CONSTRAINT generation
	 * for a given parameter
	 */
	bool couldGenerateConstraint() const;

	inline bool hasBitSizeConstraint() const
	{
		const avm_size_t dim = getBitSize();

		return( (dim > 0) && (dim <= 64) );
	}

	avm_integer_t minIntegerValue() const;

	avm_uinteger_t maxIntegerValue() const;

	virtual BF genConstraint(const BF & aParam) const;


	/**
	 * GETTER - SETTER
	 * mDefaultValue
	 */
	inline const BF & getDefaultValue() const
	{
		return( mDefaultValue );
	}

	inline bool hasDefaultValue() const
	{
		return( mDefaultValue.valid() );
	}

	inline void setDefaultValue(const BF & aDefaultValue)
	{
		mDefaultValue = aDefaultValue;
	}


	/**
	 * GETTER - SETTER
	 * mConstraint
	 */
	inline const BF & getConstraint() const
	{
		return( mConstraint );
	}

	inline bool hasConstraint() const
	{
		return( mConstraint.valid() );
	}

	inline void saveConstraint(Element * aConstraint)
	{
		mConstraint.renew( aConstraint );
	}

	inline void setConstraint(const BF & aConstraint)
	{
		mConstraint = aConstraint;
	}


	/**
	 * GETTER
	 * Refered (as typedef) TypeSpecifier
	 */
	BaseTypeSpecifier * referedTypeSpecifier();


	/**
	 * Format a value w.r.t. its type
	 */
	virtual void formatStream(OutStream & out, const BF & bfValue) const;

	virtual void formatStream(
			OutStream & out, const ArrayBF & arrayValue) const;

	/**
	 * Serialization
	 */
	inline virtual std::string strT() const
	{
		if( (mBitSize == 0) || (! isTypedNumeric()) )
		{
			return( getNameID() );
		}
		return( OSS() << getNameID() << ":" << mBitSize );
	}


	virtual void strHeader(OutStream & out) const;

	virtual void toStream(OutStream & out) const;

	virtual void toFscn(OutStream & out) const
	{
		toStream(out);
	}


public:
	static std::string TYPE_ANOMYM_ID;

	inline virtual bool isAnonymID() const
	{
		return( getNameID().empty() || (getNameID() == TYPE_ANOMYM_ID) );
	}

};


}

#endif /* BASETYPESPECIFIER_H_ */
