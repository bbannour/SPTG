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

#ifndef FML_NUMERIC_BOOST_FLOATIMPL_H_
#define FML_NUMERIC_BOOST_FLOATIMPL_H_

#include <boost/multiprecision/cpp_dec_float.hpp>
#include <boost/multiprecision/detail/default_ops.hpp>

#include <fml/numeric/Number.h>

#include <fml/numeric/Integer.h>
#include <fml/numeric/Rational.h>


namespace sep
{


class Float :
		public Number,
		public GenericNumberClass< boost::multiprecision::number<
				boost::multiprecision::cpp_dec_float<0> > , Float >
{

	AVM_DECLARE_CLONABLE_CLASS( Float )


	/**
	 * TYPEDEF
	 */
public:
	typedef boost::multiprecision::number<
					boost::multiprecision::cpp_dec_float<0> > RawValueType;

private:
	typedef  GenericNumberClass< RawValueType , Float >  ThisNumberClass;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	// RawValueType
	Float(const RawValueType & aValue)
	: Number( CLASS_KIND_T( Float ) ),
	ThisNumberClass( RawValueType( aValue ) )
	{
		//!! NOTHING
	}

	// Rational
	Float(const Rational & aRational)
	: Number( CLASS_KIND_T( Float ) ),
	ThisNumberClass( RawValueType( aRational.getValue() ) )
	{
		//!! NOTHING
	}

	// Integer
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

#ifdef _AVM_NEED_INT64_T_OVERLOADS_

	// avm_integer_t  i.e.  std::int64_t
	Float(avm_integer_t aValue)
	: Number( CLASS_KIND_T( Float ) ),
	ThisNumberClass( RawValueType( static_cast< long >(aValue) ) )
	{
		//!! NOTHING
	}

	// avm_uinteger_t  i.e.  std::uint64_t
	Float(avm_uinteger_t aValue)
	: Number( CLASS_KIND_T( Float ) ),
	ThisNumberClass( RawValueType( static_cast< unsigned long >(aValue) ) )
	{
		//!! NOTHING
	}

	// long
	Float(long aValue)
	: Number( CLASS_KIND_T( Float ) ),
	ThisNumberClass( RawValueType( aValue ) )
	{
		//!! NOTHING
	}

	Float(unsigned long aValue)
	: Number( CLASS_KIND_T( Float ) ),
	ThisNumberClass( RawValueType( aValue ) )
	{
		//!! NOTHING
	}

#else

	// avm_integer_t  i.e.  std::int64_t
	Float(avm_integer_t aValue)
	: Number( CLASS_KIND_T( Float ) ),
	ThisNumberClass( RawValueType(aValue) )
	{
		//!! NOTHING
	}

	// avm_uinteger_t  i.e.  std::uint64_t
	Float(avm_uinteger_t aValue)
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
	ThisNumberClass( RawValueType(aValue) )
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
#define CPP_FLOAT_IS_INTEGER(CPP_FLOAT, INT_T)  \
	( CPP_FLOAT == CPP_FLOAT.convert_to< INT_T >() )
//	&& boost::multiprecision::default_ops::check_in_range< INT_T >( CPP_FLOAT )

#define CPP_FLOAT_IS_POSITIVE_INTEGER(CPP_FLOAT, INT_T)  \
	( CPP_FLOAT.sign() >= 0 )  \
	&& ( CPP_FLOAT == CPP_FLOAT.convert_to< INT_T >() )
//	&& boost::multiprecision::default_ops::check_in_range< INT_T >( CPP_FLOAT )


	inline virtual bool isInt32() const
	{
		return( CPP_FLOAT_IS_INTEGER(ThisNumberClass::mValue, std::int32_t) );
	}

	inline virtual std::int32_t toInt32() const
	{
		return( ThisNumberClass::mValue.convert_to< std::int32_t >() );
	}


	inline virtual bool isInt64() const
	{
		return( CPP_FLOAT_IS_INTEGER(ThisNumberClass::mValue, std::int64_t) );
	}

	inline virtual std::int64_t toInt64() const
	{
		return( ThisNumberClass::mValue.convert_to< std::int64_t >() );
	}


	inline virtual bool isInteger() const
	{
		return( CPP_FLOAT_IS_INTEGER(ThisNumberClass::mValue, avm_integer_t) );
	}

	inline virtual avm_integer_t toInteger() const
	{
		return( ThisNumberClass::mValue.convert_to< avm_integer_t >() );
	}


	inline virtual bool isPosInteger() const
	{
		return( CPP_FLOAT_IS_POSITIVE_INTEGER(
				ThisNumberClass::mValue, avm_uinteger_t) );
	}


	inline virtual bool isUInteger() const
	{
		return( CPP_FLOAT_IS_POSITIVE_INTEGER(
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


#define CPP_FLOAT_IS_FLOAT(CPP_FLOAT, FLOAT_T)  \
	( CPP_FLOAT == CPP_FLOAT.convert_to< FLOAT_T >() )
//	&& boost::multiprecision::default_ops::check_in_range< FLOAT_T >( CPP_FLOAT )


	inline virtual bool isFloat() const
	{
//		return( false );
		return( CPP_FLOAT_IS_FLOAT(ThisNumberClass::mValue, avm_float_t) );
	}


	inline virtual avm_float_t toFloat() const
	{
		return( ThisNumberClass::mValue.convert_to< avm_float_t >() );
	}


	inline virtual bool isReal() const
	{
//		return( false );
		return( CPP_FLOAT_IS_FLOAT(ThisNumberClass::mValue, avm_real_t) );
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

	inline void set_pow(double aValue, avm_uinteger_t anExponent)
	{
		ThisNumberClass::mValue = boost::multiprecision::pow(
				RawValueType(aValue), anExponent);
	}


	/**
	 * Serialization
	 */
	virtual void toStream(OutStream & os) const override
	{
		os << TAB /*<< OS_FLOAT_PRECISION*/ << mValue.str();
		AVM_DEBUG_REF_COUNTER(os);
		os << EOL_FLUSH;
	}

	virtual std::string str() const override
	{
		return( mValue.str() );
	}

	inline virtual std::string strNum(
			std::uint8_t precision = AVM_MUMERIC_PRECISION) const
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
	return( static_cast< Float::RawValueType >( aFLoat +
			aRational.convert_to< Float::RawValueType >() ) );
}

inline Float::RawValueType operator- (Float::RawValueType aFLoat,
		const Rational::RawValueType & aRational)
{
	return( static_cast< Float::RawValueType >( aFLoat -
			aRational.convert_to< Float::RawValueType >() ) );
}

inline Float::RawValueType operator* (Float::RawValueType aFLoat,
		const Rational::RawValueType & aRational)
{
	return( static_cast< Float::RawValueType >( aFLoat *
			aRational.convert_to< Float::RawValueType >() ) );
}

inline Float::RawValueType operator/ (Float::RawValueType aFLoat,
		const Rational::RawValueType & aRational)
{
	return( static_cast< Float::RawValueType >( aFLoat /
			aRational.convert_to< Float::RawValueType >() ) );
}


} /* namespace sep */

#endif /* FML_NUMERIC_BOOST_FLOATIMPL_H_ */
