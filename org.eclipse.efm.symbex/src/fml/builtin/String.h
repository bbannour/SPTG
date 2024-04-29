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
#ifndef FML_EXPRESSION_STRING_H_
#define FML_EXPRESSION_STRING_H_

#include <fml/builtin/BuiltinForm.h>

#include <common/BF.h>


namespace sep
{

class String :
		public BuiltinForm,
		public GenericBuiltinValueString< String >
{

	AVM_DECLARE_CLONABLE_CLASS( String )


public:
	/**
	 * GLOBALS
	 */
	static const char DOUBLE_QUOTE_DELIMITER = '"';
	static const char SINGLE_QUOTE_DELIMITER = '\'';

	static char DEFAULT_DELIMITER;


	static bool USE_BACKSLASH_QUOTE;

	static bool ENABLE_QUOTE_PRINTING;

	static const char BACKSLASH_CHAR;


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
	String(const std::string & aValue, char aQuote = DEFAULT_DELIMITER)
	: BuiltinForm( CLASS_KIND_T( String ) ),
	GenericBuiltinValueString( aValue ),
	mQuoteChar( aQuote )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	String(const String & aString)
	: BuiltinForm( aString ),
	GenericBuiltinValueString( aString ),
	mQuoteChar( aString.mQuoteChar )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~String()
	{

	}


	/**
	 * mQuoteChar
	 */
	inline char getQuoteChar() const
	{
		return mQuoteChar;
	}


	inline bool isDoubleQuote() const
	{
		return( mQuoteChar == DOUBLE_QUOTE_DELIMITER );
	}

	inline bool isSingleQuote() const
	{
		return( mQuoteChar == SINGLE_QUOTE_DELIMITER );
	}


	inline void setQuoteChar(char aQuoteChar)
	{
		mQuoteChar = aQuoteChar;
	}


	/**
	 * The empty string
	 * EMPTY
	 */
	static BF _EMPTY_;


	/**
	 * LOADER - DISPOSER
	 */
	inline static void load()
	{
		_EMPTY_ = new String("");
	}

	inline static void dispose()
	{
		_EMPTY_.destroy();
	}


	/**
	 * CREATOR
	 */
	inline static BF create(const std::string & aValue,
			char aQuote = DEFAULT_DELIMITER)
	{
		return( aValue.empty() ? _EMPTY_ :
				BF(new String(aValue, aQuote)) );
	}


	/**
	 * Operation
	 */
	inline virtual std::size_t size() const override
	{
		return( mValue.size() );
	}

	/**
	 * Serialization
	 */
	inline virtual void toStream(OutStream & os) const override
	{
		if( ENABLE_QUOTE_PRINTING && (mQuoteChar != '\0') )
		{
			if( USE_BACKSLASH_QUOTE )
			{
				os << TAB << String::BACKSLASH_CHAR << mQuoteChar
						<< mValue << String::BACKSLASH_CHAR << mQuoteChar;
			}
			else
			{
				os << TAB << mQuoteChar << mValue << mQuoteChar;
			}
		}
		else
		{
			os << TAB << mValue;
		}
		AVM_DEBUG_REF_COUNTER(os);

		os << EOL_FLUSH;
	}

	inline virtual std::string str() const override
	{
		if( ENABLE_QUOTE_PRINTING && (mQuoteChar != '\0') )
		{
			if( USE_BACKSLASH_QUOTE )
			{
				return( OSS() << String::BACKSLASH_CHAR << mQuoteChar
						<< mValue << String::BACKSLASH_CHAR << mQuoteChar );
			}
			else
			{
				return( OSS() << mQuoteChar << mValue << mQuoteChar );
			}
		}
		else
		{
			return( mValue );
		}
	}

	inline virtual std::string strNum(
			std::uint8_t precision = AVM_MUMERIC_PRECISION) const override
	{
		return( str() );
	}

};


}

#endif /*FML_EXPRESSION_STRING_H_*/
