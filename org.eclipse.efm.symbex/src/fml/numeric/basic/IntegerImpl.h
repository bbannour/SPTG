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

#ifndef FML_NUMERIC_BASIC_INTEGERIMPL_H_
#define FML_NUMERIC_BASIC_INTEGERIMPL_H_

#include <fml/numeric/Number.h>


namespace sep
{

class Integer :
		public Number,
		public GenericNumberClass< avm_integer_t , Integer >
{

	AVM_DECLARE_CLONABLE_CLASS( Integer )


	/**
	 * TYPEDEF
	 */
public:
	typedef  avm_integer_t  RawValueType;

private:
	typedef  GenericNumberClass< RawValueType , Integer >  ThisNumberClass;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	// avm_integer_t  i.e.  avm_int64_t
	Integer(avm_integer_t aValue)
	: Number( CLASS_KIND_T( Integer ) ),
	ThisNumberClass( avm_integer_t(aValue) )
	{
		//!! NOTHING
	}

	// avm_uinteger_t  i.e.  avm_uint64_t
	Integer(avm_uinteger_t aValue)
	: Number( CLASS_KIND_T( Integer ) ),
	ThisNumberClass( avm_integer_t(aValue) )
	{
		//!! NOTHING
	}

#ifdef _AVM_NEED_INT64_T_OVERLOADS_

	// long
	Integer(long aValue)
	: Number( CLASS_KIND_T( Integer ) ),
	ThisNumberClass( avm_integer_t(aValue) )
	{
		//!! NOTHING
	}

	// unsigned long
	Integer(unsigned long aValue)
	: Number( CLASS_KIND_T( Integer ) ),
	ThisNumberClass( avm_integer_t(aValue) )
	{
		//!! NOTHING
	}

#endif /* _AVM_NEED_INT64_T_OVERLOADS_ */

	// int32_t
	Integer(int aValue)
	: Number( CLASS_KIND_T( Integer ) ),
	ThisNumberClass( avm_integer_t(aValue) )
	{
		//!! NOTHING
	}

	// uint32_t
	Integer(unsigned int aValue)
	: Number( CLASS_KIND_T( Integer ) ),
	ThisNumberClass( avm_integer_t(aValue) )
	{
		//!! NOTHING
	}


	Integer(const std::string & aValue)
	: Number( CLASS_KIND_T( Integer ) ),
	ThisNumberClass( sep::string_to< avm_integer_t >(aValue, std::dec) )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	Integer(const Integer & anInteger)
	: Number( anInteger ),
	ThisNumberClass( anInteger )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~Integer()
	{
		//!! NOTHING
	}


	/**
	 * BASICS TESTS
	 */
	virtual inline int sign() const
	{
		return( (ThisNumberClass::mValue < 0) ? -1 :
				(ThisNumberClass::mValue > 0) );
	}

	virtual inline bool strictlyPositive() const
	{
		return( ThisNumberClass::mValue > 0 );
	}

	virtual inline bool strictlyNegative() const
	{
		return( ThisNumberClass::mValue < 0 );
	}

	virtual inline bool isZero() const
	{
		return( ThisNumberClass::mValue == 0 );
	}

	virtual inline bool isOne() const
	{
		return( ThisNumberClass::mValue == 1 );
	}

	virtual inline bool isNegativeOne() const
	{
		return( ThisNumberClass::mValue == -1 );
	}


	/**
	 * CONVERSION
	 */
	inline virtual bool isInt32() const
	{
		return( (AVM_NUMERIC_MIN_INT32 <= ThisNumberClass::mValue) &&
				(ThisNumberClass::mValue <= AVM_NUMERIC_MAX_INT32) );
	}

	inline virtual avm_int32_t toInt32() const
	{
		return( static_cast< avm_int32_t >( ThisNumberClass::mValue ) );
	}


	inline virtual bool isInt64() const
	{
		return( (AVM_NUMERIC_MIN_INT64 <= ThisNumberClass::mValue) &&
				(ThisNumberClass::mValue <= AVM_NUMERIC_MAX_INT64) );
	}

	inline virtual avm_int64_t toInt64() const
	{
		return( static_cast< avm_int64_t >( ThisNumberClass::mValue ) );
	}


	inline virtual bool isInteger() const
	{
		return( true );
	}

	inline virtual avm_integer_t toInteger() const
	{
		return( static_cast< avm_integer_t >( ThisNumberClass::mValue ) );
	}


	inline virtual bool isPosInteger() const
	{
		return( ThisNumberClass::mValue >= 0 );
	}

	inline virtual bool isUInteger() const
	{
		return( ThisNumberClass::mValue >= 0 );
	}


	inline virtual avm_uinteger_t toUInteger() const
	{
		return( static_cast< avm_uinteger_t >( ThisNumberClass::mValue ) );
	}


	inline virtual bool isRational() const
	{
		return( true );
	}

	virtual avm_integer_t toNumerator() const
	{
		return( static_cast< avm_integer_t >( ThisNumberClass::mValue ) );
	}

	virtual avm_integer_t toDenominator() const
	{
		return( static_cast< avm_integer_t >( 1 ) );
	}


	inline virtual bool isFloat() const
	{
		return( true );
	}

	inline virtual avm_float_t toFloat() const
	{
		return( static_cast< avm_float_t >( ThisNumberClass::mValue ) );
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
	inline static avm_uinteger_t ipow(
			avm_uinteger_t aValue, avm_uinteger_t anExponent)
	{
		avm_uinteger_t aResult = 1;
		for( ; anExponent > 0; --anExponent )
		{
			aResult *= aValue;
		}

//		while( anExponent != 0 )
//		{
//			if( (anExponent & 1) == 1 )
//			{
//				aResult *= aValue;
//			}
//
//			anExponent >>= 1;
//			aValue *= aValue;
//		}

		return( aResult );
	}

	inline void set_pow(avm_uinteger_t anExponent)
	{
		ThisNumberClass::mValue =
				Integer::ipow(ThisNumberClass::mValue, anExponent);
	}

	inline void set_pow(avm_uinteger_t aValue, avm_uinteger_t anExponent)
	{
		ThisNumberClass::mValue = Integer::ipow(aValue, anExponent);
	}


	inline Integer pow(avm_uinteger_t anExponent) const
	{
		return( Integer( Integer::ipow(ThisNumberClass::mValue, anExponent) ) );
	}

	inline static Integer pow(avm_uinteger_t aValue, avm_uinteger_t anExponent)
	{
		return( Integer( Integer::ipow(aValue, anExponent) ) );
	}


	/**
	 * Serialization
	 */
	inline void toStream(OutStream & os) const
	{
		os << TAB << mValue;
		AVM_DEBUG_REF_COUNTER(os);
		os << EOL << std::flush;
	}

	virtual std::string str() const
	{
		return( OSS() << mValue );
	}

	inline virtual std::string strNum(
			avm_uint8_t precision = AVM_MUMERIC_PRECISION) const
	{
		return( OSS() << mValue );
	}

};


} /* namespace sep */

#endif /* FML_NUMERIC_BASIC_INTEGERIMPL_H_ */
