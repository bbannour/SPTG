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
#ifndef FML_EXPRESSION_IDENTIFIER_H_
#define FML_EXPRESSION_IDENTIFIER_H_

#include <fml/builtin/BuiltinForm.h>


namespace sep
{

class Identifier :
		public BuiltinForm,
		public GenericBuiltinValueString< Identifier >,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( Identifier )
{

	AVM_DECLARE_CLONABLE_CLASS( Identifier )


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Identifier(const std::string & aValue)
	: BuiltinForm( CLASS_KIND_T( Identifier ) ),
	GenericBuiltinValueString( aValue )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	Identifier(const Identifier & anIdentifier)
	: BuiltinForm( anIdentifier ),
	GenericBuiltinValueString( anIdentifier )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~Identifier()
	{
		//!! NOTHING
	}


	/**
	 * Serialization
	 */
	inline virtual void toStream(OutStream & os) const override
	{
		os << TAB << mValue;
		AVM_DEBUG_REF_COUNTER(os);
		os << EOL_FLUSH;
	}

	inline virtual std::string str() const override
	{
		return( mValue );
	}

	inline virtual std::string strNum(
			std::uint8_t precision = AVM_MUMERIC_PRECISION) const override
	{
		return( mValue );
	}



};

}

#endif /*FML_EXPRESSION_IDENTIFIER_H_*/
