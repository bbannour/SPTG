/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 26 mars 2013
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef FML_EXPRESSION_NUMBER_H_
#define FML_EXPRESSION_NUMBER_H_

#include <fml/builtin/BuiltinForm.h>


namespace sep
{

class Number  :  public BuiltinForm ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( Number )
{

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Number(class_kind_t aClassKind)
	: BuiltinForm( aClassKind )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	Number(const Number & aNumber)
	: BuiltinForm( aNumber )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~Number()
	{
		//!! NOTHING
	}


	/**
	 * SIGN TESTS
	 */
	virtual int sign() const = 0;


	inline virtual bool isPositive() const
	{
		return( sign() >= 0 );
	}

	inline virtual bool strictlyPositive() const
	{
		return( sign() > 0 );
	}


	inline virtual bool isNegative() const
	{
		return( sign() <= 0 );
	}

	inline virtual bool strictlyNegative() const
	{
		return( sign() < 0 );
	}


	/**
	 * BASICS TESTS
	 */
	virtual bool isZero() const = 0;

	virtual bool isOne() const = 0;

	virtual bool isNegativeOne() const = 0;


	/**
	 * CONVERSION
	 */
	virtual bool isInt32() const = 0;
	virtual std::int32_t toInt32() const = 0;

	virtual bool isInt64() const = 0;
	virtual std::int64_t toInt64() const = 0;


	virtual bool isInteger() const = 0;
	virtual avm_integer_t toInteger() const = 0;

	virtual bool isUInteger() const = 0;
	virtual avm_uinteger_t toUInteger() const = 0;


	virtual bool isRational() const = 0;
	virtual avm_integer_t toDenominator() const = 0;
	virtual avm_integer_t toNumerator() const = 0;


	virtual bool isFloat() const = 0;
	virtual avm_float_t toFloat() const = 0;

	virtual bool isReal() const = 0;
	virtual avm_real_t toReal() const = 0;


//	/**
//	 * INCREMENT
//	 * DECREMENT
//	 */
//	virtual void addExpr(avm_integer_t aValue = 1) = 0;
//	virtual void minExpr(avm_integer_t aValue = 1) = 0;
//
//	/**
//	 * uminus
//	 */
//	virtual void uminus() = 0;

};


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// GENERIC BUILTIN FORM
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

template< typename Value_T , class Class_T >
class GenericNumberClass
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
	GenericNumberClass(const Value_T & aValue)
	: mValue( aValue )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	GenericNumberClass(const GenericNumberClass & aNumber)
	: mValue( aNumber.mValue )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~GenericNumberClass()
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
	 * INCREMENT
	 * DECREMENT
	 */
#ifdef _AVM_NEED_INT64_T_OVERLOADS_

	void addExpr(avm_integer_t aValue = 1)
	{
		mValue = (mValue + static_cast< long >( aValue ));
	}

	void minExpr(avm_integer_t aValue = 1)
	{
		mValue = (mValue - static_cast< long >( aValue ));
	}

#else

	void addExpr(avm_integer_t aValue = 1)
	{
		mValue = (mValue + aValue);
	}

	void minExpr(avm_integer_t aValue = 1)
	{
		mValue = (mValue - aValue);
	}

#endif /* _AVM_NEED_INT64_T_OVERLOADS_ */


	/**
	 * uminus
	 */
	void uminus()
	{
		mValue = (- mValue);
	}


	/**
	 * ASSIGN
	 * OPERATOR
	 */
	template< class Number_T >
	Class_T & operator=(const Number_T & x)
	{
		if( this == &x )
		{
			return *this;
		}

		mValue = x.mValue;

		return( *this );
	}


	template< class Number_T >
	Class_T & operator+=(const Number_T & other)
	{
		mValue += other.mValue;

		return( *this );
	}

	template< class Number_T >
	Class_T & operator-=(const Number_T & other)
	{
		mValue -= other.mValue;

		return( *this );
	}


	template< class Number_T >
	Class_T & operator*=(const Number_T & other)
	{
		mValue *= other.mValue;

		return( *this );
	}

	template< class Number_T >
	Class_T & operator/=(const Number_T & other)
	{
		mValue /= other.mValue;

		return( *this );
	}


	/**
	 * ARITHMETIC
	 * OPERATOR
	 */
	Class_T operator-() const
	{
		return( Class_T( - mValue ) );
	}

	template< class Number_T >
	Class_T operator+(const Number_T & other) const
	{
		return( Class_T( mValue + other.mValue ) );
	}

	template< class Number_T >
	Class_T operator-(const Number_T & other) const
	{
		return( Class_T( mValue - other.mValue ) );
	}


	template< class Number_T >
	Class_T operator*(const Number_T & other) const
	{
		return( Class_T( mValue * other.mValue ) );
	}

	template< class Number_T >
	Class_T operator/(const Number_T & other) const
	{
		return( Class_T( mValue / other.mValue ) );
	}


	/**
	 * COMPARISON
	 * OPERATOR
	 */
	// EQUAL
	template< class Number_T >
	inline bool operator==(const Number_T & other) const
	{
		return( mValue == other.mValue );
	}

	template< class Number_T >
	inline bool isEQ(const Number_T & other) const
	{
		return( mValue == other.mValue );
	}


	// NOT EQUAL
	template< class Number_T >
	inline bool operator!=(const Number_T & other) const
	{
		return( mValue != other.mValue );
	}

	template< class Number_T >
	inline bool isNEQ(const Number_T & other) const
	{
		return( mValue != other.mValue );
	}


	// COMPARE
	template< class Number_T >
	inline int compare(const Number_T & other) const
	{
		return( (mValue  < other.getValue()) ? -1 :
				(mValue == other.getValue()) ?  0 : 1 );
	}


	// < <= > >=
	template< class Number_T >
	bool operator< (const Number_T & other) const
	{
		return( mValue < other.mValue );
	}

	template< class Number_T >
	bool operator<=(const Number_T & other) const
	{
		return( mValue <= other.mValue );
	}

	template< class Number_T >
	bool operator> (const Number_T & other) const
	{
		return( mValue > other.mValue );
	}

	template< class Number_T >
	bool operator>=(const Number_T & other) const
	{
		return( mValue >= other.mValue );
	}

};


} /* namespace sep */
#endif /* FML_EXPRESSION_NUMBER_H_ */
