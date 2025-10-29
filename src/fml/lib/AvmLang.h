/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 2 avr. 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVMLANG_H_
#define AVMLANG_H_

#include <string>

#include <util/avm_numeric.h>
#include <common/BF.h>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
// GENERIC XLIA SYNTAX
////////////////////////////////////////////////////////////////////////////////

class XLIA_SYNTAX
{

public:
	////////////////////////////////////////////////////////////////////////////
	// LOADER / DISPOSER  API
	////////////////////////////////////////////////////////////////////////////
	static void load();
	static void dispose();

public:
	static BF ID_ALL;
};




////////////////////////////////////////////////////////////////////////////////
// EXPRESSION IMPLEMENTATION KIND
////////////////////////////////////////////////////////////////////////////////

class EXPRESSION
{

public:

	enum IMPLEMENTATION_KIND
	{
		NATIVE_IMPL,

		GINAC_IMPL,

		CVC4_IMPL,

		UNDEFINED_IMPL
	};

};



////////////////////////////////////////////////////////////////////////////////
// VARIABLE DATA
////////////////////////////////////////////////////////////////////////////////

class IPointerVariableNature
{

public:

	enum POINTER_VARIABLE_NATURE
	{
		POINTER_STANDARD_NATURE,

		POINTER_UFI_OFFSET_NATURE,

		POINTER_UFI_MIXED_NATURE,

		POINTER_UFI_RUNTIME_NATURE,

		POINTER_ENUM_SYMBOL_NATURE,

		POINTER_FIELD_ARRAY_INDEX_NATURE,
		POINTER_FIELD_ARRAY_OFFSET_NATURE,

		POINTER_FIELD_CLASS_ATTRIBUTE_NATURE,

		POINTER_FIELD_CHOICE_ATTRIBUTE_NATURE,

		POINTER_FIELD_UNION_ATTRIBUTE_NATURE,

		POINTER_UNDEFINED_NATURE
	};

	/**
	 * DESTRUCTOR
	 */
	virtual ~IPointerVariableNature()
	{
		//!! NOTHING
	}

	/**
	 * STATIC
	 */
	static std::string strPointerDataNature(POINTER_VARIABLE_NATURE aNature);

	static std::string strPointer(const POINTER_VARIABLE_NATURE aNature);


	/**
	 * API
	 */
	virtual POINTER_VARIABLE_NATURE getPointerNature() const = 0;


	inline bool hasArrayIndexPointer() const
	{
		return( (getPointerNature() == POINTER_FIELD_ARRAY_INDEX_NATURE) ||
				(getPointerNature() == POINTER_UFI_MIXED_NATURE) );
	}

	inline bool isFieldArrayIndexPointer() const
	{
		return( getPointerNature() == POINTER_FIELD_ARRAY_INDEX_NATURE );
	}

	inline bool isFieldArrayOffsetPointer() const
	{
		return( getPointerNature() == POINTER_FIELD_ARRAY_OFFSET_NATURE );
	}


	inline bool isFieldClassAttributePointer() const
	{
		return( getPointerNature() == POINTER_FIELD_CLASS_ATTRIBUTE_NATURE );
	}

	inline bool isFieldChoiceAttributePointer() const
	{
		return( getPointerNature() == POINTER_FIELD_CHOICE_ATTRIBUTE_NATURE );
	}

	inline bool isFieldUnionAttributePointer() const
	{
		return( getPointerNature() == POINTER_FIELD_UNION_ATTRIBUTE_NATURE );
	}


	inline bool isEnumSymbolPointer() const
	{
		return( getPointerNature() == POINTER_ENUM_SYMBOL_NATURE );
	}


	inline bool isUfiOffsetPointer() const
	{
		return( getPointerNature() == POINTER_UFI_OFFSET_NATURE );
	}

	inline bool isUfiMixedPointer() const
	{
		return( getPointerNature() == POINTER_UFI_MIXED_NATURE );
	}

	inline bool isUfiRuntimePointer() const
	{
		return( getPointerNature() == POINTER_UFI_RUNTIME_NATURE );
	}

	inline bool isStandardPointer() const
	{
		return( getPointerNature() == POINTER_STANDARD_NATURE );
	}


};



} /* namespace sep */
#endif /* AVMLANG_H_ */
