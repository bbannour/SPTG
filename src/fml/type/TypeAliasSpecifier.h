/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 15 janv. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef TYPEALIASSPECIFIER_H_
#define TYPEALIASSPECIFIER_H_

#include <fml/type/BaseTypeSpecifier.h>

#include <fml/type/TypeSpecifier.h>


namespace sep
{

class ArrayBF;
class DataType;


class TypeAliasSpecifier : public BaseTypeSpecifier ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( TypeAliasSpecifier )
{

	AVM_DECLARE_UNCLONABLE_CLASS(TypeAliasSpecifier)


protected:
	/*
	 * ATTRIBUTES
	 */
	// the Type Specifier
	const TypeSpecifier mTargetSpecifierType;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	TypeAliasSpecifier(const DataType & astType,
			const TypeSpecifier & aTypeSpecifier)
	: BaseTypeSpecifier(CLASS_KIND_T( TypeAliasSpecifier ),
			TYPE_ALIAS_SPECIFIER, astType, aTypeSpecifier),
	mTargetSpecifierType( aTypeSpecifier )
	{
		//!!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~TypeAliasSpecifier()
	{
		//!!! NOTHING
	}


	/**
	 * GETTER - SETTER
	 * mTargetSpecifierType
	 */
	inline const TypeSpecifier & getTargetTypeSpecifier() const
	{
		return( mTargetSpecifierType );
	}

	inline const BaseTypeSpecifier & targetTypeSpecifier() const
	{
		return( mTargetSpecifierType.is< TypeAliasSpecifier >() ?
				mTargetSpecifierType.alias().targetTypeSpecifier()
				: mTargetSpecifierType );
	}

	inline virtual bool isTypeAlias() const override
	{
		return( true );
	}

	/**
	 * GETTER - SETTER
	 * mSpecifierKind
	 */
	inline virtual avm_type_specifier_kind_t getTypeSpecifierKind() const override
	{
		return( mTargetSpecifierType.getTypeSpecifierKind() );
	}


	/**
	 * CONSTRAINT generation
	 * for a given parameter
	 */
	inline virtual BF genConstraint(const BF & aParam) const override
	{
		if( hasConstraint() )
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "TODO << TypeAliasSpecifier::genConstraint( "
					<< aParam << " ) >> with compiled constraint:" << std::endl
					<< getConstraint()
					<< SEND_EXIT;
		}

		return( mTargetSpecifierType.genConstraint(aParam) );
	}


	/**
	 * Format a value w.r.t. its type
	 */
	inline virtual void formatStream(
			OutStream & os, const BF & bfValue) const override
	{
		mTargetSpecifierType.formatStream(os, bfValue);
	}

	inline virtual void formatStream(
			OutStream & os, const ArrayBF & arrayValue) const override
	{
		mTargetSpecifierType.formatStream(os, arrayValue);
	}

	/**
	 * Serialization
	 */
	virtual std::string strT() const override
	{
		return( getNameID() );
	}

	virtual void toStream(OutStream & os) const override;

};


} /* namespace sep */

#endif /* TYPEALIASSPECIFIER_H_ */
