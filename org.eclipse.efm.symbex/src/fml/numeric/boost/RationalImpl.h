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

#ifndef FML_NUMERIC_BOOST_RATIONALIMPL_H_
#define FML_NUMERIC_BOOST_RATIONALIMPL_H_

#include <boost/multiprecision/cpp_int.hpp>
#include <boost/multiprecision/detail/default_ops.hpp>

#include <fml/numeric/Number.h>

#include <fml/numeric/Integer.h>

#include <cmath>


namespace sep
{


class Rational :
		public Number,
		public GenericNumberClass< boost::multiprecision::cpp_rational , Rational >
{

	AVM_DECLARE_CLONABLE_CLASS( Rational )


	/**
	 * TYPEDEF
	 */
public:
	typedef  boost::multiprecision::cpp_rational  RawValueType;

private:
	typedef  GenericNumberClass< RawValueType , Rational >  ThisNumberClass;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	// RawValueType
	Rational(const RawValueType & aValue)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( aValue )
	{
		simplif();
	}

	// Integer / Integer
	Rational(const Integer & aNumerator, const Integer & aDenominator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType(
			aNumerator.getValue(), aDenominator.getValue() ) )
	{
		simplif();
	}

	// Integer::RawValueType / Integer::RawValueType
	// i.e boost::multiprecision::cpp_int / boost::multiprecision::cpp_int
	Rational(const Integer::RawValueType & aNumerator,
			const Integer::RawValueType & aDenominator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType(aNumerator, aDenominator) )
	{
		simplif();
	}

	// avm_integer_t / avm_integer_t  i.e.  std::int64_t / std::int64_t
	Rational(avm_integer_t aNumerator, avm_integer_t aDenominator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType(
			Integer::RawValueType( aNumerator ),
			Integer::RawValueType( aDenominator ) ) )
	{
		simplif();
	}

	// avm_integer_t / avm_uinteger_t  i.e.  std::int64_t / std::uint64_t
	Rational(avm_integer_t aNumerator, avm_uinteger_t aDenominator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType(
			Integer::RawValueType( aNumerator ),
			Integer::RawValueType( aDenominator ) ) )
	{
		simplif();
	}

	// avm_uinteger_t / avm_integer_t  i.e.  std::uint64_t / std::int64_t
	Rational(avm_uinteger_t aNumerator, avm_integer_t aDenominator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType(
			Integer::RawValueType( aNumerator ),
			Integer::RawValueType( aDenominator ) ) )
	{
		simplif();
	}

	// avm_uinteger_t / avm_uinteger_t  i.e.  std::uint64_t / std::uint64_t
	Rational(avm_uinteger_t aNumerator, avm_uinteger_t aDenominator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType(
			Integer::RawValueType( aNumerator ),
			Integer::RawValueType( aDenominator ) ) )
	{
		//!! NOTHING
	}

	// std::string / avm_integer_t  i.e.  std::string / std::int64_t
	Rational(const std::string & aNumerator, avm_integer_t aDenominator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType(
			Integer::RawValueType( aNumerator ),
			Integer::RawValueType( aDenominator ) ) )
	{
		simplif();
	}

	// avm_integer_t / std::string  i.e.  std::int64_t / std::string
	Rational(avm_integer_t aNumerator, const std::string & aDenominator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType(
			Integer::RawValueType( aNumerator ),
			Integer::RawValueType( aDenominator ) ) )
	{
		simplif();
	}

	// std::string / std::string
	Rational(const std::string & aNumerator, const std::string & aDenominator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType(
			Integer::RawValueType(aNumerator),
			Integer::RawValueType(aDenominator) ) )
	{
		simplif();
	}

	// Integer
	Rational(const Integer & aNumerator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType( aNumerator.getValue() ) )
	{
		simplif();
	}

	// Integer::RawValueType i.e boost::multiprecision::cpp_int
	Rational(const Integer::RawValueType & aNumerator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType(aNumerator) )
	{
		simplif();
	}

	// avm_integer_t i.e. std::int64_t
	Rational(avm_integer_t aNumerator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType( Integer::RawValueType( aNumerator ) ) )
	{
		simplif();
	}

	// avm_uinteger_t i.e. std::uint64_t
	Rational(avm_uinteger_t aNumerator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType( Integer::RawValueType( aNumerator ) ) )
	{
		simplif();
	}

#ifdef _AVM_NEED_INT64_T_OVERLOADS_

	// long
	Rational(long aNumerator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType( Integer::RawValueType(aNumerator) ) )
	{
		simplif();
	}

	// unsigned long
	Rational(unsigned long aNumerator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType( Integer::RawValueType(aNumerator) ) )
	{
		simplif();
	}

#endif /* _AVM_NEED_INT64_T_OVERLOADS_ */

	// int32_t
	Rational(int aNumerator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType( Integer::RawValueType(aNumerator) ) )
	{
		simplif();
	}

	// uint32_t
	Rational(unsigned int aNumerator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType( Integer::RawValueType(aNumerator) ) )
	{
		simplif();
	}

	// std::string
	Rational(const std::string & aRational)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType( ) )
	{
		fromString(ThisNumberClass::mValue, aRational);

		simplif();
	}


	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	Rational(const Rational & aRational)
	: Number( aRational ),
	ThisNumberClass( aRational )
	{
		simplif();
	}


	inline static void fromString(RawValueType & rop, const std::string & aValue)
	{
		std::string::size_type pos = aValue.find_first_of("/.");
		if( pos != std::string::npos)
		{
			if( aValue[pos] == '/' )
			{
				rop = RawValueType( aValue );
			}
			else //if( aValue[pos] == '.' )
			{
				Integer aNumer( std::string(aValue).erase(pos, 1) );

				Integer aDenom = Integer::pow(10, aValue.size() - (pos + 1));

				rop = RawValueType( aNumer.getValue(), aDenom.getValue() );
			}
		}
		else
		{
			rop = RawValueType( aValue );
		}
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~Rational()
	{
		//!! NOTHING
	}


	/**
	 * GETTER - SETTER
	 * ThisNumberClass::mValue
	 */
	bool simplif()
	{
		return( true );
	}


	/**
	 * GETTER - SETTER
	 * ThisNumberClass::mValue
	 */
	inline Integer getNumerator() const
	{
		return( Integer( boost::multiprecision::numerator(
				ThisNumberClass::mValue ) ) );
	}

	inline Integer getDenominator() const
	{
		return( Integer( boost::multiprecision::denominator(
				ThisNumberClass::mValue ) ) );
	}


	inline Integer::RawValueType rawNumerator() const
	{
		return( boost::multiprecision::numerator(
				ThisNumberClass::mValue ) );
	}

	inline Integer::RawValueType rawDenominator() const
	{
		return( boost::multiprecision::denominator(
				ThisNumberClass::mValue ) );
	}


	inline void setValue(avm_integer_t aNumerator, avm_integer_t aDenominator)
	{
		ThisNumberClass::mValue = RawValueType(
				Integer::RawValueType( aNumerator ),
				Integer::RawValueType( aDenominator ) );
	}


	inline void setValue(avm_integer_t aValue)
	{
		ThisNumberClass::mValue = RawValueType( Integer(aValue).getValue() );
	}


	/**
	 * BASICS TESTS
	 */
	inline virtual int sign() const
	{
		return( ThisNumberClass::mValue.sign() );
	}

	inline virtual bool isZero() const
	{
		return( ThisNumberClass::mValue.is_zero() );
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
#define CPP_RAT_IS_INTEGER(RAT_NUM_INT, RAT_DEN_INT, INT_T)  \
	( RAT_DEN_INT == 1 )  \
	&& ( RAT_NUM_INT == RAT_NUM_INT.convert_to< INT_T >() )
//	&& boost::multiprecision::default_ops::check_in_range< INT_T >( RAT_NUM_INT )

#define CPP_RAT_IS_POSITIVE_INTEGER(RAT_NUM_INT, RAT_DEN_INT, INT_T)  \
	( RAT_NUM_INT.sign() >= 0 )  \
	&& ( RAT_DEN_INT == 1 )  \
	&& ( RAT_NUM_INT == RAT_NUM_INT.convert_to< INT_T >() )
//	&& boost::multiprecision::default_ops::check_in_range< INT_T >( RAT_NUM_INT )


	inline virtual bool isInt32() const
	{
		return( CPP_RAT_IS_INTEGER(
				rawNumerator(), rawDenominator(), std::int32_t) );
	}

	inline virtual std::int32_t toInt32() const
	{
		return( ThisNumberClass::mValue.convert_to< std::int32_t >() );
	}


	inline virtual bool isInt64() const
	{
		return( CPP_RAT_IS_INTEGER(
				rawNumerator(), rawDenominator(), std::int64_t) );
	}

	inline virtual std::int64_t toInt64() const
	{
		return( ThisNumberClass::mValue.convert_to< std::int64_t >() );
	}


	inline virtual bool isInteger() const
	{
		return( CPP_RAT_IS_INTEGER(
				rawNumerator(), rawDenominator(), avm_integer_t) );
	}

	inline virtual avm_integer_t toInteger() const
	{
		return( ThisNumberClass::mValue.convert_to< avm_integer_t >() );
	}


	inline virtual bool isPosInteger() const
	{
		return( CPP_RAT_IS_POSITIVE_INTEGER(
				rawNumerator(), rawDenominator(), avm_uinteger_t) );
	}


	inline virtual bool isUInteger() const
	{
		return( CPP_RAT_IS_POSITIVE_INTEGER(
				rawNumerator(), rawDenominator(), avm_uinteger_t) );
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
		Integer::RawValueType num = boost::multiprecision::pow(
				boost::multiprecision::numerator(ThisNumberClass::mValue),
				anExponent);

		Integer::RawValueType den = boost::multiprecision::pow(
				boost::multiprecision::denominator(ThisNumberClass::mValue),
				anExponent);

		ThisNumberClass::mValue = boost::multiprecision::cpp_rational(num, den);
	}


	/**
	 * Serialization
	 */
	inline void toStream(OutStream & os) const
	{
		os << TAB << ThisNumberClass::mValue;
		AVM_DEBUG_REF_COUNTER(os);
		os << EOL_FLUSH;
	}

	virtual std::string str() const override
	{
		if( rawDenominator() != 1 )
		{
			return( OSS() << rawNumerator() << '/' << rawDenominator() );
		}
		else
		{
			return( OSS() << rawNumerator() );
		}
	}

	inline virtual std::string strNum(
			std::uint8_t precision = AVM_MUMERIC_PRECISION) const
	{
		if( rawDenominator() != 1 )
		{
			return( OSS() << rawNumerator() << '/' << rawDenominator() );
		}
		else
		{
			return( OSS() << rawNumerator() );
		}
	}

	inline virtual std::string strNumerator(
			std::uint8_t precision = AVM_MUMERIC_PRECISION) const
	{
		return( OSS() << rawNumerator() );
	}

	inline virtual std::string strDenominator(
			std::uint8_t precision = AVM_MUMERIC_PRECISION) const
	{
		return( OSS() << rawDenominator() );
	}

};


} /* namespace sep */

#endif /* FML_NUMERIC_BOOST_RATIONALIMPL_H_ */
