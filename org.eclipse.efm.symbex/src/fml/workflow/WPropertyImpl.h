/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 24 mars 2016
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef FML_WORKFLOW_WPROPERTYIMPL_H_
#define FML_WORKFLOW_WPROPERTYIMPL_H_

#include <common/BF.h>

#include <fml/builtin/String.h>


namespace sep
{

class AvmCode;
class BFCode;

class Operator;

class WObject;


class WPropertyImpl
{

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	WPropertyImpl()
	{
			//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~WPropertyImpl()
	{
		//!! NOTHING
	}


	/**
	 * API
	 * getValue()
	 */
	virtual const BF & getValue() const = 0;

	/**
	 * GETTER - SETTER
	 * getValue()
	 */

	inline std::string strValue() const
	{
		return( getValue().str() );
	}



	/**
	 * GETTER - SETTER
	 * any Type Value
	 */
	template<class T >
	inline T * getValue() const
	{
		return( getValue().as_ptr< T >() );
	}

	template<class T >
	inline bool hasValue() const
	{
		return( getValue().is< T >() );
	}


	/**
	 * GETTER - SETTER
	 * for BOOLEAN attribue
	 */
	inline bool getBooleanValue() const
	{
		return( getValue().toBoolean() );
	}

	/**
	 * GETTER - SETTER
	 * for CHARACTER attribue
	 */
	char getCharacterValue() const
	{
		return( getValue().toCharacter() );
	}


	/**
	 * GETTER - SETTER
	 * for INTEGER attribue
	 */
	inline avm_integer_t getIntegerValue() const
	{
		return( getValue().toInteger() );
	}

	inline avm_int32_t getInt32Value() const
	{
		return( getValue().toInt32() );
	}

	inline avm_int64_t getInt64Value() const
	{
		return( getValue().toInt64() );
	}


	/**
	 * GETTER - SETTER
	 * for FLOAT attribue
	 */
	inline avm_float_t getFloatValue() const
	{
		return( getValue().toFloat() );
	}


	/**
	 * GETTER - SETTER
	 * for STRING attribue
	 */
	inline std::string getStringValue() const
	{
		return( getValue().toBuiltinString() );
	}

	inline bool hasStringValue() const
	{
		return( getValue().is< String >() );
	}


	/**
	 * GETTER - SETTER
	 * for STRING_ID attribue
	 */
	inline std::string getIdentifierValue() const
	{
		return( getValue().toIdentifier() );
	}


	/**
	 * GETTER - SETTER
	 * for STRING_UFI attribue
	 */
	inline std::string getUfiValue() const
	{
		return( getValue().toUfi() );
	}


	/**
	 * GETTER - SETTER
	 * for AvmCode attribue
	 */
	const BFCode & getAvmCodeValue() const;

	bool hasAvmCodeValue() const;


	/**
	 * GETTER
	 * for BuiltinArray attribute
	 */
	BuiltinArray * getBuiltinArrayValue() const;

	bool hasBuiltinArrayValue() const;

	BF getArrayValue() const;

	bool hasArrayValue() const;


	inline std::string toStringValue(avm_size_t offset) const
	{
		return( toStringValue(getBuiltinArrayValue(), offset) );
	}

	std::string toStringValue(BuiltinArray * anArray, avm_size_t offset) const;


	/**
	 * Serialization
	 */
	inline static std::string toStringValue(const BF & aValue)
	{
		if( aValue.is< String >() )
		{
			return( aValue.to_ptr< String >()->getValue() );
		}

		return( aValue.str() );
	}

	inline virtual std::string toStringValue() const
	{
		return( toStringValue( getValue() ) );
	}

};


} /* namespace sep */

#endif /* FML_WORKFLOW_WPROPERTYIMPL_H_ */
