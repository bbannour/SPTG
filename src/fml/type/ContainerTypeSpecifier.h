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


class ContainerTypeSpecifier final : public BaseTypeSpecifier ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( ContainerTypeSpecifier )
{

	AVM_DECLARE_UNCLONABLE_CLASS(ContainerTypeSpecifier)


protected:
	/*
	 * ATTRIBUTES
	 */
	// the Type Specifier
	const TypeSpecifier mContentsTypeSpecifier;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ContainerTypeSpecifier(avm_type_specifier_kind_t aSpecifierKind,
			const DataType & astType,
			const TypeSpecifier & aTypeSpecifier, std::size_t aSize)
	: BaseTypeSpecifier(CLASS_KIND_T( ContainerTypeSpecifier ), aSpecifierKind,
			astType, aSize, aSize * ( aTypeSpecifier.valid() ?
					aTypeSpecifier.getDataSize() : 1 ) + 1, 0),
	mContentsTypeSpecifier( aTypeSpecifier )
	{
		//!!! NOTHING
	}

	ContainerTypeSpecifier(avm_type_specifier_kind_t aSpecifierKind,
			const std::string & aTypeID,
			const TypeSpecifier & aTypeSpecifier, std::size_t aSize)
	: BaseTypeSpecifier(CLASS_KIND_T( ContainerTypeSpecifier ), aSpecifierKind,
			aTypeID, aSize, ( aSize * (aTypeSpecifier.valid() ?
					aTypeSpecifier.getDataSize() : 1) + 1 ), 0),
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



	/**
	 * GETTER - SETTER
	 * the Bloc Data Size
	 */
	inline std::size_t bsize()
	{
		return( mContentsTypeSpecifier.getDataSize() );
	}


	/**
	 * CONSTRAINT generation
	 * for a given parameter
	 */
	virtual bool couldGenerateConstraint() const override;

	virtual BF genConstraint(const BF & aParam) const override;


	/**
	 * Format a value w.r.t. its type
	 */
	inline virtual void formatStream(
			OutStream & os, const ArrayBF & arrayValue) const override;

	// Due to [-Woverloaded-virtual=]
	using BaseTypeSpecifier::formatStream;


	/**
	 * Serialization
	 */
	static std::string strSpecifierKing(avm_type_specifier_kind_t aSpecifierKind);

	inline std::string strSpecifierKing() const
	{
		return( ContainerTypeSpecifier::strSpecifierKing( getTypeSpecifierKind() ) );
	}

	std::string strType() const;

	std::string strT() const override
	{
		return( isAnonymID() ? strType() : getNameID() );
	}

	void toStream(OutStream & os) const override;

};


}

#endif /* CONTAINERCONTAINERTYPESPECIFIER_H_ */
