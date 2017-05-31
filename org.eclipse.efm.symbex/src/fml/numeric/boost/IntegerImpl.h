/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 17 mai 2016
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and Implementation
 ******************************************************************************/

#ifndef FML_NUMERIC_BOOST_INTEGERIMPL_H_
#define FML_NUMERIC_BOOST_INTEGERIMPL_H_

#include <boost/multiprecision/cpp_int.hpp>
#include <boost/multiprecision/detail/default_ops.hpp>
#include <boost/multiprecision/cpp_dec_float.hpp>

#include <fml/numeric/Number.h>


namespace sep
{


class Integer :
		public Number,
		public GenericNumberClass< boost::multiprecision::cpp_int , Integer >
{

	AVM_DECLARE_CLONABLE_CLASS( Integer )


	/**
	 * TYPEDEF
	 */
public:
	typedef  boost::multiprecision::cpp_int  RawValueType;

private:
	typedef  GenericNumberClass< RawValueType , Integer >  ThisNumberClass;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Integer(const RawValueType & aValue)
	: Number( CLASS_KIND_T( Integer ) ),
	ThisNumberClass( aValue )
	{
		//!! NOTHING
	}

#ifdef _AVM_NEED_INT64_T_OVERLOADS_

	// avm_integer_t  i.e.  avm_int64_t
	Integer(avm_integer_t aValue)
	: Number( CLASS_KIND_T( Integer ) ),
	ThisNumberClass( RawValueType( static_cast< long >( aValue ) ) )
	{
		//!! NOTHING
	}

	// avm_uinteger_t  i.e.  avm_uint64_t
	Integer(avm_uinteger_t aValue)
	: Number( CLASS_KIND_T( Integer ) ),
	ThisNumberClass( RawValueType( static_cast< unsigned long >( aValue ) ) )
	{
		//!! NOTHING
	}

	// long
	Integer(long aValue)
	: Number( CLASS_KIND_T( Integer ) ),
	ThisNumberClass( RawValueType( aValue ) )
	{
		//!! NOTHING
	}

	Integer(unsigned long aValue)
	: Number( CLASS_KIND_T( Integer ) ),
	ThisNumberClass( RawValueType( aValue ) )
	{
		//!! NOTHING
	}

#else

	// avm_integer_t  i.e.  avm_int64_t
	Integer(avm_integer_t aValue)
	: Number( CLASS_KIND_T( Integer ) ),
	ThisNumberClass( RawValueType(aValue) )
	{
		//!! NOTHING
	}

	// avm_uinteger_t  i.e.  avm_uint64_t
	Integer(avm_uinteger_t aValue)
	: Number( CLASS_KIND_T( Integer ) ),
	ThisNumberClass( RawValueType(aValue) )
	{
		//!! NOTHING
	}

#endif /* _AVM_NEED_INT64_T_OVERLOADS_ */

	// int32_t
	Integer(int aValue)
	: Number( CLASS_KIND_T( Integer ) ),
	ThisNumberClass( RawValueType(aValue) )
	{
		//!! NOTHING
	}

	// uint32_t
	Integer(unsigned int aValue)
	: Number( CLASS_KIND_T( Integer ) ),
	ThisNumberClass( RawValueType(aValue) )
	{
		//!! NOTHING
	}

	// std::string
	Integer(const std::string & aValue)
	: Number( CLASS_KIND_T( Integer ) ),
	ThisNumberClass( RawValueType(aValue) )
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
		return( ThisNumberClass::mValue.sign() );
	}

	virtual inline bool isZero() const
	{
		return( ThisNumberClass::mValue.is_zero() );
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
#define CPP_INT_IS_INTEGER(CPP_INT, INT_T)  \
	( CPP_INT == CPP_INT.convert_to< INT_T >() )
//	&& boost::multiprecision::default_ops::check_in_range< INT_T >( CPP_INT )

#define CPP_INT_IS_POSITIVE_INTEGER(CPP_INT, INT_T)  \
	( CPP_INT.sign() >= 0 )  \
	&& ( CPP_INT == CPP_INT.convert_to< INT_T >() )
//	&& boost::multiprecision::default_ops::check_in_range< INT_T >( CPP_INT )


	inline virtual bool isInt32() const
	{
		return( CPP_INT_IS_INTEGER(ThisNumberClass::mValue, avm_int32_t) );
	}

	inline virtual avm_int32_t toInt32() const
	{
		return( ThisNumberClass::mValue.convert_to< avm_int32_t >() );
	}


	inline virtual bool isInt64() const
	{
		return( CPP_INT_IS_INTEGER(ThisNumberClass::mValue, avm_int64_t) );
	}

	inline virtual avm_int64_t toInt64() const
	{
		return( ThisNumberClass::mValue.convert_to< avm_int64_t >() );
	}


	inline virtual bool isInteger() const
	{
		return( CPP_INT_IS_INTEGER(ThisNumberClass::mValue, avm_integer_t) );
	}

	inline virtual avm_integer_t toInteger() const
	{
		return( ThisNumberClass::mValue.convert_to< avm_integer_t >() );
	}


	inline virtual bool isPosInteger() const
	{
		return( CPP_INT_IS_POSITIVE_INTEGER(
				ThisNumberClass::mValue, avm_uinteger_t) );
	}


	inline virtual bool isUInteger() const
	{
		return( CPP_INT_IS_POSITIVE_INTEGER(
				ThisNumberClass::mValue, avm_uinteger_t) );
	}

	inline virtual avm_uinteger_t toUInteger() const
	{
		return( ThisNumberClass::mValue.convert_to< avm_uinteger_t >() );
	}


	inline virtual bool isRational() const
	{
		return( isInteger() );
	}

	virtual avm_integer_t toNumerator() const
	{
		return( ThisNumberClass::mValue.convert_to< avm_integer_t >() );
	}

	virtual avm_integer_t toDenominator() const
	{
		return( static_cast< avm_integer_t >( 1 ) );
	}


#define CPP_INT_IS_FLOAT(CPP_INT, FLOAT_T)  \
	boost::multiprecision::default_ops::check_in_range< FLOAT_T >(  \
	CPP_INT.convert_to< boost::multiprecision::cpp_dec_float<0> >() )
//	( CPP_INT == CPP_INT.convert_to< FLOAT_T >() )


	inline virtual bool isFloat() const
	{
		return( false );
//		return( CPP_INT_IS_FLOAT(ThisNumberClass::mValue, avm_float_t) );
	}


	inline virtual avm_float_t toFloat() const
	{
		return( ThisNumberClass::mValue.convert_to< avm_float_t >() );
	}


	inline virtual bool isReal() const
	{
		return( false );
//		return( CPP_INT_IS_FLOAT(ThisNumberClass::mValue, avm_real_t) );
	}

	inline virtual avm_real_t toReal() const
	{
		return( ThisNumberClass::mValue.convert_to< avm_real_t >() );
	}


	/**
	 * math function
	 */
	inline void set_pow(avm_uinteger_t anExponent)
	{
		ThisNumberClass::mValue = boost::multiprecision::pow(
				ThisNumberClass::mValue, anExponent);
	}

	inline void set_pow(avm_uinteger_t aValue, avm_uinteger_t anExponent)
	{
		ThisNumberClass::mValue = boost::multiprecision::pow(
				RawValueType(aValue), anExponent);
	}


	inline Integer pow(avm_uinteger_t anExponent) const
	{
		return( Integer( boost::multiprecision::pow(
				ThisNumberClass::mValue, anExponent) ) );
	}

	inline static Integer pow(avm_uinteger_t aValue, avm_uinteger_t anExponent)
	{
		return( Integer( boost::multiprecision::pow(
				RawValueType(aValue), anExponent) ) );
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

#endif /* FML_NUMERIC_BOOST_INTEGERIMPL_H_ */
