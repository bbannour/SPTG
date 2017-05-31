/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 10 mai 2016
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and Implementation
 ******************************************************************************/

#ifndef FML_NUMERIC_BASIC_FLOATIMPL_H_
#define FML_NUMERIC_BASIC_FLOATIMPL_H_

#include <fml/numeric/Number.h>

#include <fml/numeric/Integer.h>
#include <fml/numeric/Rational.h>

#include <cmath>

namespace sep
{


class Float :
		public Number,
		public GenericNumberClass< avm_float_t , Float >
{

	AVM_DECLARE_CLONABLE_CLASS( Float )


	/**
	 * TYPEDEF
	 */
public:
	typedef  avm_float_t  RawValueType;

private:
	typedef  GenericNumberClass< RawValueType , Float >  ThisNumberClass;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Float(const Rational & aRational)
	: Number( CLASS_KIND_T( Float ) ),
	ThisNumberClass( RawValueType( aRational.toFloat() ) )
	{
		//!! NOTHING
	}

	Float(const Integer & anInteger)
	: Number( CLASS_KIND_T( Float ) ),
	ThisNumberClass( RawValueType( anInteger.getValue() ) )
	{
		//!! NOTHING
	}


	// avm_float_t  i.e.  double
	Float(avm_float_t aValue)
	: Number( CLASS_KIND_T( Float ) ),
	ThisNumberClass( RawValueType(aValue) )
	{
		//!! NOTHING
	}

	// float
	Float(float aValue)
	: Number( CLASS_KIND_T( Float ) ),
	ThisNumberClass( RawValueType(aValue) )
	{
		//!! NOTHING
	}

	// avm_integer_t  i.e.  avm_int64_t
	Float(avm_integer_t aValue)
	: Number( CLASS_KIND_T( Float ) ),
	ThisNumberClass( RawValueType(aValue) )
	{
		//!! NOTHING
	}

	// avm_uinteger_t  i.e.  avm_uint64_t
	Float(avm_uinteger_t aValue)
	: Number( CLASS_KIND_T( Float ) ),
	ThisNumberClass( RawValueType(aValue) )
	{
		//!! NOTHING
	}

#ifdef _AVM_NEED_INT64_T_OVERLOADS_

	// long
	Float(long aValue)
	: Number( CLASS_KIND_T( Float ) ),
	ThisNumberClass( RawValueType(aValue) )
	{
		//!! NOTHING
	}

	Float(unsigned long aValue)
	: Number( CLASS_KIND_T( Float ) ),
	ThisNumberClass( RawValueType(aValue) )
	{
		//!! NOTHING
	}

#endif /* _AVM_NEED_INT64_T_OVERLOADS_ */

	// int32_t
	Float(int aValue)
	: Number( CLASS_KIND_T( Float ) ),
	ThisNumberClass( RawValueType(aValue) )
	{
		//!! NOTHING
	}

	// uint32_t
	Float(unsigned int aValue)
	: Number( CLASS_KIND_T( Float ) ),
	ThisNumberClass( RawValueType(aValue) )
	{
		//!! NOTHING
	}

	// std::string
	Float(const std::string & aValue)
	: Number( CLASS_KIND_T( Float ) ),
	ThisNumberClass( sep::string_to< avm_float_t >(aValue, std::dec) )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	Float(const Float & aFloat)
	: Number( aFloat ),
	ThisNumberClass( aFloat )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~Float()
	{
		//!! NOTHING
	}


	/**
	 * BASICS TESTS
	 */
	inline virtual int sign() const
	{
		return( (ThisNumberClass::mValue < 0) ? -1 :
				(ThisNumberClass::mValue > 0) );
	}


	inline virtual bool isPositive() const
	{
		return( ThisNumberClass::mValue >= 0 );
	}

	inline virtual bool strictlyPositive() const
	{
		return( ThisNumberClass::mValue > 0 );
	}


	inline virtual bool isNegative() const
	{
		return( ThisNumberClass::mValue <= 0 );
	}

	inline virtual bool strictlyNegative() const
	{
		return( ThisNumberClass::mValue < 0 );
	}


	inline virtual bool isZero() const
	{
		return( ThisNumberClass::mValue == 0 );
	}

	inline virtual bool isOne() const
	{
		return( ThisNumberClass::mValue == 1 );
	}

	inline virtual bool isNegativeOne() const
	{
		return( ThisNumberClass::mValue == -1 );
	}


	/**
	 * CONVERSION
	 */
	inline virtual bool isInt32() const
	{
		return( (ThisNumberClass::mValue ==
					static_cast< avm_int32_t >( ThisNumberClass::mValue )) &&
				(AVM_NUMERIC_MIN_INT <= ThisNumberClass::mValue) &&
				(ThisNumberClass::mValue <= AVM_NUMERIC_MAX_INT) );
	}

	inline virtual avm_int32_t toInt32() const
	{
		return( static_cast< avm_int32_t >( ThisNumberClass::mValue ) );
	}

	inline virtual bool isInt64() const
	{
		return( (ThisNumberClass::mValue ==
					static_cast< avm_int64_t >( ThisNumberClass::mValue )) &&
				(AVM_NUMERIC_MIN_LONG <= ThisNumberClass::mValue) &&
				(ThisNumberClass::mValue <= AVM_NUMERIC_MIN_LONG) );
	}

	inline virtual avm_int64_t toInt64() const
	{
		return( static_cast< avm_int64_t >( ThisNumberClass::mValue ) );
	}


	inline virtual bool isInteger() const
	{
		return( ThisNumberClass::mValue ==
				static_cast< avm_integer_t >( ThisNumberClass::mValue ) );
	}

	inline virtual avm_integer_t toInteger() const
	{
		return( static_cast< avm_integer_t >( ThisNumberClass::mValue ) );
	}


	inline virtual bool isPosInteger() const
	{
		return( ThisNumberClass::mValue ==
				static_cast< avm_uinteger_t >( ThisNumberClass::mValue ) );
	}


	inline virtual bool isUInteger() const
	{
		return( ThisNumberClass::mValue ==
				static_cast< avm_uinteger_t >( ThisNumberClass::mValue ) );
	}

	inline virtual avm_uinteger_t toUInteger() const
	{
		return( static_cast< avm_uinteger_t >( ThisNumberClass::mValue ) );
	}


	inline virtual bool isRational() const
	{
		return( true );
	}

	virtual avm_integer_t toDenominator() const
	{
		return( static_cast< avm_integer_t >( ThisNumberClass::mValue ) );
	}

	virtual avm_integer_t toNumerator() const
	{
		return( static_cast< avm_integer_t >( ThisNumberClass::mValue ) );
	}


	inline virtual bool isFloat() const
	{
		return( true );
	}

	inline virtual avm_float_t toFloat() const
	{
		return( ThisNumberClass::mValue );
	}


	inline virtual bool isReal() const
	{
		return( true );
	}

	inline virtual avm_real_t toReal() const
	{
		return( static_cast< avm_real_t >( ThisNumberClass::mValue ) );
	}


	/**
	 * math function
	 */
	inline void set_pow(avm_uinteger_t anExponent)
	{
		ThisNumberClass::mValue = std::pow(ThisNumberClass::mValue, anExponent);
	}

	inline void set_pow(double aValue, avm_uinteger_t anExponent)
	{
		ThisNumberClass::mValue = std::pow(aValue, anExponent);
	}


	/**
	 * Serialization
	 */
	virtual void toStream(OutStream & os) const
	{
		os << TAB << OS_FLOAT_PRECISION << mValue;
		AVM_DEBUG_REF_COUNTER(os);
		os << EOL_FLUSH;
	}

	virtual std::string str() const
	{
		return( OSS() << OS_REAL_PRECISION << mValue );
	}

	inline virtual std::string strNum(
			avm_uint8_t precision = AVM_MUMERIC_PRECISION) const
	{
		return( OSS() << std::fixed
				<< std::setprecision( precision ) << mValue );
	}

};


/**
 * Operators
 */
inline Float::RawValueType operator+ (Float::RawValueType aFLoat,
		const Rational::RawValueType & aRational)
{
	return( static_cast< Float::RawValueType >( aFLoat + aRational.toFloat() ) );
}

inline Float::RawValueType operator- (Float::RawValueType aFLoat,
		const Rational::RawValueType & aRational)
{
	return( static_cast< Float::RawValueType >( aFLoat - aRational.toFloat() ) );
}

inline Float::RawValueType operator* (Float::RawValueType aFLoat,
		const Rational::RawValueType & aRational)
{
	return( static_cast< Float::RawValueType >( aFLoat * aRational.toFloat() ) );
}

inline Float::RawValueType operator/ (Float::RawValueType aFLoat,
		const Rational::RawValueType & aRational)
{
	return( static_cast< Float::RawValueType >( aFLoat / aRational.toFloat() ) );
}


} /* namespace sep */

#endif /* FML_NUMERIC_BASIC_FLOATIMPL_H_ */
