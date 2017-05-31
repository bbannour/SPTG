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
	TypeSpecifier mTargetSpecifierType;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	TypeAliasSpecifier(DataType * aCompiledType,
			const TypeSpecifier & aTypeSpecifier)
	: BaseTypeSpecifier(CLASS_KIND_T( TypeAliasSpecifier ),
			TYPE_ALIAS_SPECIFIER, aCompiledType, aTypeSpecifier),
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
	inline const TypeSpecifier & getTargetTypeSpecifier()
	{
		return( mTargetSpecifierType );
	}

	inline BaseTypeSpecifier * targetTypeSpecifier()
	{
		return( mTargetSpecifierType.is< TypeAliasSpecifier >() ?
				mTargetSpecifierType.alias().targetTypeSpecifier()
				: mTargetSpecifierType );
	}

	inline bool hasTargetTypeSpecifier() const
	{
		return( mTargetSpecifierType.valid() );
	}

	inline void setTargetTypeSpecifier(const TypeSpecifier & aTypeSpecifier)
	{
		mTargetSpecifierType = aTypeSpecifier;
	}


	/**
	 * CONSTRAINT generation
	 * for a given parameter
	 */
	inline BF genConstraint(const BF & aParam) const
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
	inline virtual void formatStream(OutStream & os, const BF & bfValue) const
	{
		mTargetSpecifierType.formatStream(os, bfValue);
	}

	inline virtual void formatStream(
			OutStream & os, const ArrayBF & arrayValue) const
	{
		mTargetSpecifierType.formatStream(os, arrayValue);
	}

	/**
	 * Serialization
	 */
	virtual std::string strT() const
	{
		return( getNameID() );
	}

	virtual void toStream(OutStream & os) const;

};


} /* namespace sep */

#endif /* TYPEALIASSPECIFIER_H_ */
