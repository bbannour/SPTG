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

#ifndef CONTAINERTYPESPECIFIER_H_
#define CONTAINERTYPESPECIFIER_H_

#include <fml/type/BaseTypeSpecifier.h>

#include <fml/type/TypeSpecifier.h>


namespace sep
{


class ArrayBF;
class DataType;


class ContainerTypeSpecifier : public BaseTypeSpecifier ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( ContainerTypeSpecifier )
{

	AVM_DECLARE_UNCLONABLE_CLASS(ContainerTypeSpecifier)


protected:
	/*
	 * ATTRIBUTES
	 */
	// the Type Specifier
	TypeSpecifier mContentsTypeSpecifier;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ContainerTypeSpecifier(avm_type_specifier_kind_t aSpecifierKind,
			DataType * aCompiledType,
			const TypeSpecifier & aTypeSpecifier, avm_size_t aSize)
	: BaseTypeSpecifier(CLASS_KIND_T( ContainerTypeSpecifier ),
			aSpecifierKind, aCompiledType, aSize,
			aSize * (aTypeSpecifier.valid() ?
					aTypeSpecifier.getDataSize() : 1) + 1, 0),
	mContentsTypeSpecifier( aTypeSpecifier )
	{
		//!!! NOTHING
	}

	ContainerTypeSpecifier(avm_type_specifier_kind_t aSpecifierKind,
			const std::string & aTypeID, const TypeSpecifier & aTypeSpecifier,
			avm_size_t aSize)
	: BaseTypeSpecifier(CLASS_KIND_T( ContainerTypeSpecifier ),
			aSpecifierKind, aTypeID, aSize,
			aSize * (aTypeSpecifier.valid() ?
					aTypeSpecifier.getDataSize() : 1) + 1, 0),
	mContentsTypeSpecifier( aTypeSpecifier )
	{
		//!!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~ContainerTypeSpecifier()
	{
		//!!! NOTHING
	}


	/**
	 * GETTER - SETTER
	 * mContentsTypeSpecifier
	 */
	inline const TypeSpecifier & getContentsTypeSpecifier() const
	{
		return( mContentsTypeSpecifier );
	}

	inline bool hasContentsTypeSpecifier() const
	{
		return( mContentsTypeSpecifier.valid() );
	}

	inline void setContentsTypeSpecifier(const TypeSpecifier & aTypeSpecifier)
	{
		mContentsTypeSpecifier = aTypeSpecifier;
	}


	/**
	 * GETTER - SETTER
	 * the Bloc Data Size
	 */
	inline avm_size_t bsize()
	{
		return( mContentsTypeSpecifier.valid() ?
				mContentsTypeSpecifier.getDataSize() : 1 );
	}


	/**
	 * CONSTRAINT generation
	 * for a given parameter
	 */
	BF genConstraint(const BF & aParam) const;


	/**
	 * Format a value w.r.t. its type
	 */
	inline virtual void formatStream(
			OutStream & os, const ArrayBF & arrayValue) const;


	/**
	 * Serialization
	 */
	static std::string strSpecifierKing(avm_type_specifier_kind_t aSpecifierKind);

	std::string strType() const;

	std::string strT() const
	{
		return( isAnonymID() ? strType() : getNameID() );
	}

	void toStream(OutStream & os) const;

};


}

#endif /* CONTAINERCONTAINERTYPESPECIFIER_H_ */
