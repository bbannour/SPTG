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
#ifndef FML_EXPRESSION_BOOLEAN_H_
#define FML_EXPRESSION_BOOLEAN_H_

#include <fml/builtin/BuiltinForm.h>


namespace sep
{


class Boolean :
		public BuiltinForm,
		public GenericBuiltinValue< bool , Boolean >
{

	AVM_DECLARE_CLONABLE_CLASS( Boolean )


private:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Boolean(bool aValue)
	: BuiltinForm( CLASS_KIND_T( Boolean ) ),
	GenericBuiltinValue( aValue )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	Boolean(const Boolean & aBoolean)
	: BuiltinForm( aBoolean ),
	GenericBuiltinValue( aBoolean )
	{
		//!! NOTHING
	}


public:
	/**
	 * CREATOR
	 */
	inline static Boolean * create(bool aValue)
	{
		return( new Boolean(aValue) );
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~Boolean()
	{
		//!! NOTHING
	}


	/**
	 * VALUE TEST
	 */
	inline virtual bool isEqualFalse() const
	{
		return( ! mValue );
	}

	inline virtual bool isNotEqualFalse() const
	{
		return( mValue );
	}


	inline virtual bool isEqualTrue() const
	{
		return( mValue );
	}

	inline virtual bool isNotEqualTrue() const
	{
		return( ! mValue );
	}


	/**
	 * Serialization
	 */
	inline void toStream(OutStream & os) const
	{
		os << TAB << ( mValue ? "true" : "false" );
		AVM_DEBUG_REF_COUNTER(os);
		os << EOL << std::flush;
	}

	virtual std::string str() const
	{
		return( mValue ? "true" : "false" );
	}

	inline virtual std::string strNum(
			avm_uint8_t precision = AVM_MUMERIC_PRECISION) const
	{
		return( mValue ? "true" : "false" );
	}

};


}

#endif /*FML_EXPRESSION_BOOLEAN_H_*/
