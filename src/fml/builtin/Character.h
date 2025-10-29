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
#ifndef FML_EXPRESSION_CHARACTER_H_
#define FML_EXPRESSION_CHARACTER_H_

#include <fml/builtin/BuiltinForm.h>


namespace sep
{

class Character :
		public BuiltinForm,
		public GenericBuiltinValue< char , Character >
{

	AVM_DECLARE_CLONABLE_CLASS( Character )


protected:
	/**
	 * ATTRIBUTES
	 */
	char mQuoteChar;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Character(char aValue, char aQuote = '\'')
	: BuiltinForm( CLASS_KIND_T( Character ) ),
	GenericBuiltinValue( aValue ),
	mQuoteChar( aQuote )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	Character(const Character & aCharacter)
	: BuiltinForm( aCharacter ),
	GenericBuiltinValue( aCharacter ),
	mQuoteChar( aCharacter.mQuoteChar )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~Character()
	{
		//!! NOTHING
	}


	/**
	 * Serialization
	 */
	inline virtual void toStream(OutStream & os) const override
	{
		os << TAB << mQuoteChar << mValue << mQuoteChar;
		AVM_DEBUG_REF_COUNTER(os);
		os << EOL_FLUSH;
	}

	inline virtual std::string str() const override
	{
		return( OSS() << mQuoteChar << mValue << mQuoteChar );
	}

	inline std::string strChar(char aQuote = '\'') const
	{
		return( OSS() << aQuote << mValue << aQuote );
	}

	inline virtual std::string strNum(
			std::uint8_t precision = AVM_MUMERIC_PRECISION) const override
	{
		return( OSS() << mQuoteChar << mValue << mQuoteChar );
	}

};


}

#endif /*FML_EXPRESSION_CHARACTER_H_*/
