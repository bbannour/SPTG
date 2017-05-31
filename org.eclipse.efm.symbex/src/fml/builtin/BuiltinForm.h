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
#ifndef FML_EXPRESSION_BUILTIN_H_
#define FML_EXPRESSION_BUILTIN_H_

#include <common/Element.h>
#include <common/AvmPointer.h>


namespace sep
{


class BuiltinForm : public Element ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( BuiltinForm )
{


public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BuiltinForm(class_kind_t aClassKind)
	: Element( aClassKind )
	{
			//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	BuiltinForm(const BuiltinForm & aBuiltin)
	: Element( aBuiltin )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~BuiltinForm()
	{
		//!! NOTHING
	}


	/**
	 * COMPARISON
	 * OPERATOR
	 */

//	virtual bool isEQ(const Element & bf) const = 0;
//
//	virtual bool isNEQ(const Element & bf) const = 0;


	/**
	 * SERIALIZATION
	 */
	virtual void toStream(OutStream & os) const = 0;

protected:
	/**
	 * ATTRIBUTES
	 */

};




////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// GENERIC BUILTIN FORM
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

template< typename Value_T , class Class_T >
class GenericBuiltinValue
{

protected:
	/**
	 * ATTRIBUTES
	 */
	Value_T mValue;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	GenericBuiltinValue(Value_T aValue)
	: mValue( aValue )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	GenericBuiltinValue(const GenericBuiltinValue & aBuiltin)
	: mValue( aBuiltin.mValue )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~GenericBuiltinValue()
	{
		//!! NOTHING
	}


	/**
	 * GETTER - SETTER
	 * mValue
	 */
	inline Value_T & getValue()
	{
		return( mValue );
	}

	inline const Value_T & getValue() const
	{
		return( mValue );
	}

	inline void setValue(Value_T aValue)
	{
		mValue = aValue;
	}


	/**
	 * COMPARISON
	 * OPERATOR
	 */
	inline int compare(const Class_T & other) const
	{
		return( (mValue == other.mValue )? 0 :
				((mValue < other.mValue ) ? -1 : 1) );
	}

	inline bool operator==(const Class_T & other) const
	{
		return( mValue == other.mValue );
	}

	inline bool isEQ(const Class_T & other) const
	{
		return( mValue == other.mValue );
	}

	inline bool isNEQ(const Class_T & other) const
	{
		return( mValue != other.mValue );
	}

};



template< class Class_T >
class GenericBuiltinValueString :
		public GenericBuiltinValue< std::string , Class_T >
{

public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	GenericBuiltinValueString(const std::string & aValue)
	: GenericBuiltinValue< std::string , Class_T >( aValue )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	GenericBuiltinValueString(const GenericBuiltinValueString & aBuiltin)
	: GenericBuiltinValue< std::string , Class_T >( aBuiltin )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~GenericBuiltinValueString()
	{
		//!! NOTHING
	}


	/**
	 * COMPARISON
	 * OPERATOR
	 */

	inline int compare(const Class_T & other) const
	{
		return( GenericBuiltinValue< std::string , Class_T >::
				mValue.compare( other.mValue ) );
	}

};


}

#endif /*FML_EXPRESSION_BUILTIN_H_*/
